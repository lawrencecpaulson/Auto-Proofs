theory Roth_Disjoint_Index
  imports Roth_Index
begin

section \<open>Products in disjoint sets of variables\<close>

lemma roth_lookup_zero_outside:
  assumes "Poly_Mapping.keys I \<subseteq> A" "v \<notin> A"
  shows "Poly_Mapping.lookup I v = 0"
  using assms by (metis not_in_keys_iff_lookup_eq_zero subsetD)

lemma roth_disjoint_exponent_left:
  fixes I J I2 J2 :: "nat \<Rightarrow>\<^sub>0 nat"
  assumes ia: "Poly_Mapping.keys I \<subseteq> A"
    and i2a: "Poly_Mapping.keys I2 \<subseteq> A"
    and jb: "Poly_Mapping.keys J \<subseteq> B"
    and j2b: "Poly_Mapping.keys J2 \<subseteq> B"
    and ab: "A \<inter> B = {}"
    and eq: "I + J = I2 + J2"
  shows "I = I2"
proof (rule Poly_Mapping.poly_mapping_eqI)
  fix v
  have eqv: "Poly_Mapping.lookup I v + Poly_Mapping.lookup J v =
    Poly_Mapping.lookup I2 v + Poly_Mapping.lookup J2 v"
    using eq by (metis lookup_add)
  show "Poly_Mapping.lookup I v = Poly_Mapping.lookup I2 v"
  proof (cases "v \<in> A")
    case True
    then have nb: "v \<notin> B" using ab by auto
    have j0: "Poly_Mapping.lookup J v = 0"
      by (rule roth_lookup_zero_outside[OF jb nb])
    have j20: "Poly_Mapping.lookup J2 v = 0"
      by (rule roth_lookup_zero_outside[OF j2b nb])
    show ?thesis using eqv by (simp add: j0 j20)
  next
    case False
    have i0: "Poly_Mapping.lookup I v = 0"
      by (rule roth_lookup_zero_outside[OF ia False])
    have i20: "Poly_Mapping.lookup I2 v = 0"
      by (rule roth_lookup_zero_outside[OF i2a False])
    show ?thesis by (simp add: i0 i20)
  qed
qed

lemma roth_exponent_add_left_cancel:
  fixes I J K :: "nat \<Rightarrow>\<^sub>0 nat"
  assumes "I + J = I + K"
  shows "J = K"
proof (rule Poly_Mapping.poly_mapping_eqI)
  fix v
  have "Poly_Mapping.lookup I v + Poly_Mapping.lookup J v =
    Poly_Mapping.lookup I v + Poly_Mapping.lookup K v"
    using assms by (metis lookup_add)
  then show "Poly_Mapping.lookup J v = Poly_Mapping.lookup K v"
    by simp
qed

lemma roth_disjoint_exponent_unique:
  fixes I J I2 J2 :: "nat \<Rightarrow>\<^sub>0 nat"
  assumes ia: "Poly_Mapping.keys I \<subseteq> A"
    and i2a: "Poly_Mapping.keys I2 \<subseteq> A"
    and jb: "Poly_Mapping.keys J \<subseteq> B"
    and j2b: "Poly_Mapping.keys J2 \<subseteq> B"
    and ab: "A \<inter> B = {}"
    and eq: "I + J = I2 + J2"
  shows "I = I2 \<and> J = J2"
proof -
  have i: "I = I2"
    by (rule roth_disjoint_exponent_left[OF ia i2a jb j2b ab eq])
  have e2: "I2 + J = I2 + J2" using eq i by simp
  have j: "J = J2"
    by (rule roth_exponent_add_left_cancel[OF e2])
  show ?thesis using i j by simp
qed

lemma roth_disjoint_prod_coeff:
  fixes P Q :: "'a::idom mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
    and i: "I \<in> Poly_Mapping.keys (mapping_of P)"
    and j: "J \<in> Poly_Mapping.keys (mapping_of Q)"
  shows "coeff (P * Q) (I + J) = coeff P I * coeff Q J"
proof -
  have uniq: "I + J = I2 + J2 \<longleftrightarrow> I = I2 \<and> J = J2"
    if i2: "I2 \<in> Poly_Mapping.keys (mapping_of P)"
      and j2: "J2 \<in> Poly_Mapping.keys (mapping_of Q)"
    for I2 J2
    using roth_disjoint_exponent_unique
      [of I "vars P" I2 J "vars Q" J2] disj i j i2 j2
    by (auto simp: vars_def)
  have inner:
    "(\<Sum>v\<in>Poly_Mapping.keys (mapping_of Q).
      Poly_Mapping.lookup (mapping_of Q) v when I + J = t + v) =
      (if t = I then coeff Q J else 0)"
    if t: "t \<in> Poly_Mapping.keys (mapping_of P)" for t
    using uniq[OF t] by (simp add: when_def coeff_def sum.If_cases j)
  show ?thesis
    unfolding coeff_def times_mpoly.rep_eq lookup_times
    by (simp add: inner i sum.If_cases if_distrib coeff_def)
qed

lemma roth_select_lookup:
  fixes P :: "'k \<Rightarrow>\<^sub>0 'a::comm_monoid_add"
  shows "(\<Sum>x\<in>Poly_Mapping.keys P \<inter> {I}.
    Poly_Mapping.lookup P x) = Poly_Mapping.lookup P I"
  by (cases "I \<in> Poly_Mapping.keys P")
    (simp_all add: not_in_keys_iff_lookup_eq_zero)

lemma roth_disjoint_prod_coeff_ambient:
  fixes P Q :: "'a::idom mpoly"
  assumes pa: "vars P \<subseteq> A"
    and qb: "vars Q \<subseteq> B"
    and isupp: "Poly_Mapping.keys I \<subseteq> A"
    and jsupp: "Poly_Mapping.keys J \<subseteq> B"
    and disj: "A \<inter> B = {}"
  shows "coeff (P * Q) (I + J) = coeff P I * coeff Q J"
proof -
  have uniq: "I + J = I2 + J2 \<longleftrightarrow> I = I2 \<and> J = J2"
    if i2: "I2 \<in> Poly_Mapping.keys (mapping_of P)"
      and j2: "J2 \<in> Poly_Mapping.keys (mapping_of Q)"
    for I2 J2
    using roth_disjoint_exponent_unique
      [of I A I2 J B J2]
      pa qb disj isupp jsupp i2 j2
    by (auto simp: vars_def)
  have inner:
    "(\<Sum>v\<in>Poly_Mapping.keys (mapping_of Q).
      Poly_Mapping.lookup (mapping_of Q) v when I + J = t + v) =
      (if t = I then coeff Q J else 0)"
    if t: "t \<in> Poly_Mapping.keys (mapping_of P)" for t
    using uniq[OF t]
    by (simp add: when_def coeff_def sum.If_cases
      roth_select_lookup)
  show ?thesis
    unfolding coeff_def times_mpoly.rep_eq lookup_times
    by (simp add: inner sum.If_cases if_distrib coeff_def
      roth_select_lookup sum_distrib_right[symmetric])
qed

lemma roth_disjoint_taylor_coeff:
  fixes P Q :: "'a::idom mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
    and i: "roth_taylor_coeff a I P \<noteq> 0"
    and j: "roth_taylor_coeff a J Q \<noteq> 0"
  shows "roth_taylor_coeff a (I + J) (P * Q) =
    roth_taylor_coeff a I P * roth_taylor_coeff a J Q"
  using roth_disjoint_prod_coeff
    [of "roth_translate a P" "roth_translate a Q" I J] assms
  by (simp add: roth_taylor_coeff_def roth_translate_mult
    roth_vars_translate coeff_def in_keys_iff)

lemma roth_disjoint_index_mult_nonzero:
  fixes P Q :: "'a::idom mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
    and p: "P \<noteq> 0"
    and q: "Q \<noteq> 0"
  shows "roth_index m r a (P * Q) =
    roth_index m r a P + roth_index m r a Q"
proof -
  obtain I where i: "roth_taylor_coeff a I P \<noteq> 0"
    and ie: "roth_index m r a P = ereal (roth_weight m r I)"
    using roth_index_attained[OF p] by blast
  obtain J where j: "roth_taylor_coeff a J Q \<noteq> 0"
    and je: "roth_index m r a Q = ereal (roth_weight m r J)"
    using roth_index_attained[OF q] by blast
  have cij: "roth_taylor_coeff a (I + J) (P * Q) \<noteq> 0"
    using roth_disjoint_taylor_coeff[OF disj i j] i j by simp
  have le: "roth_index m r a (P * Q) \<le>
    ereal (roth_weight m r (I + J))"
    by (rule roth_index_le_coeff[OF cij])
  have le2: "roth_index m r a (P * Q) \<le>
    roth_index m r a P + roth_index m r a Q"
    using le by (simp add: ie je roth_weight_add)
  show ?thesis
    by (rule order_antisym[OF le2 roth_index_mult])
qed

lemma roth_disjoint_index_mult:
  fixes P Q :: "'a::idom mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
  shows "roth_index m r a (P * Q) =
    roth_index m r a P + roth_index m r a Q"
proof (cases "P = 0 \<or> Q = 0")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis
    using roth_disjoint_index_mult_nonzero[OF disj] by blast
qed

end
