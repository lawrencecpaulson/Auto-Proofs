theory Roth_Tensor_Determinant
  imports Roth_Tensor_Split
begin

section \<open>Hasse derivatives and variable support\<close>

lemma roth_hasse_index_vars:
  fixes P :: "rat mpoly"
  assumes nz: "roth_hasse J P \<noteq> 0"
  shows "Poly_Mapping.keys J \<subseteq> vars P"
proof
  fix v
  assume vj: "v\<in>Poly_Mapping.keys J"
  obtain I where ci: "MPoly_Type.coeff (roth_hasse J P) I \<noteq> 0"
    using nz coeff_all_0 by blast
  have cp: "MPoly_Type.coeff P (I+J) \<noteq> 0"
    by (rule roth_hasse_coeff_support[OF ci])
  have key: "I+J \<in> Poly_Mapping.keys (mapping_of P)"
    using cp by (simp add: MPoly_Type.coeff_def in_keys_iff)
  have vk: "v\<in>Poly_Mapping.keys (I+J)"
    using vj by (simp add: in_keys_iff lookup_add)
  show "v\<in>vars P" using key vk by (auto simp: vars_def)
qed

lemma roth_hasse_zero_outside_vars:
  fixes P :: "rat mpoly"
  assumes "\<not> Poly_Mapping.keys J \<subseteq> vars P"
  shows "roth_hasse J P = 0"
  using assms roth_hasse_index_vars by blast

lemma roth_hasse_last_zero_left:
  fixes P :: "rat mpoly"
  assumes pv: "vars P \<subseteq> {..<n}" and j: "j>0"
  shows "roth_hasse (Poly_Mapping.single n j) P = 0"
proof (rule roth_hasse_zero_outside_vars)
  have "n\<in>Poly_Mapping.keys (Poly_Mapping.single n j)"
    using j by (simp add: in_keys_iff lookup_single when_def)
  moreover have "n\<notin>vars P" using pv by auto
  ultimately show
    "\<not> Poly_Mapping.keys (Poly_Mapping.single n j) \<subseteq> vars P"
    by blast
qed

lemma roth_hasse_left_zero_right:
  fixes Q :: "rat mpoly"
  assumes ji: "Poly_Mapping.keys J \<subseteq> {..<n}"
    and j: "J\<noteq>0" and qv: "vars Q \<subseteq> {n}"
  shows "roth_hasse J Q = 0"
proof (rule roth_hasse_zero_outside_vars)
  show "\<not> Poly_Mapping.keys J \<subseteq> vars Q"
  proof
    assume h: "Poly_Mapping.keys J \<subseteq> vars Q"
    have emp: "Poly_Mapping.keys J = {}"
      using ji h qv by (auto simp del: Poly_Mapping.keys_eq_empty)
    have "J=0" using emp by simp
    then show False using j by blast
  qed
qed

lemma roth_single_support_lookup_zero:
  assumes b: "Poly_Mapping.keys B \<subseteq> {n}" and vn: "v\<noteq>n"
  shows "Poly_Mapping.lookup B v=0"
  using b vn by (auto simp: in_keys_iff)

lemma roth_left_support_lookup_zero:
  assumes a: "Poly_Mapping.keys A \<subseteq> {..<n}"
    and nv: "\<not> v<n"
  shows "Poly_Mapping.lookup A v=0"
  using a nv by (auto simp: in_keys_iff)

lemma roth_split_index_unique:
  fixes n :: nat
  assumes a: "Poly_Mapping.keys A \<subseteq> {..<n}"
    and b: "Poly_Mapping.keys B \<subseteq> {n}"
    and c: "Poly_Mapping.keys C \<subseteq> {..<n}"
    and d: "Poly_Mapping.keys D \<subseteq> {n}"
    and eq: "A+B=C+D"
  shows "A=C \<and> B=D"
proof -
  have ev: "Poly_Mapping.lookup A v + Poly_Mapping.lookup B v =
    Poly_Mapping.lookup C v + Poly_Mapping.lookup D v" for v
    using arg_cong[OF eq, of
      "\<lambda>F. Poly_Mapping.lookup F v"]
    by (simp add: lookup_add)
  have ac: "A=C"
  proof (rule poly_mapping_eqI)
    fix v
    show "Poly_Mapping.lookup A v = Poly_Mapping.lookup C v"
    proof (cases "v<n")
      case True
      have vn: "v\<noteq>n" using True by simp
      have bz: "Poly_Mapping.lookup B v=0"
        by (rule roth_single_support_lookup_zero[OF b vn])
      have dz: "Poly_Mapping.lookup D v=0"
        by (rule roth_single_support_lookup_zero[OF d vn])
      show ?thesis using ev[of v] bz dz by simp
    next
      case False
      have az: "Poly_Mapping.lookup A v=0"
        by (rule roth_left_support_lookup_zero[OF a False])
      have cz: "Poly_Mapping.lookup C v=0"
        by (rule roth_left_support_lookup_zero[OF c False])
      show ?thesis using az cz by simp
    qed
  qed
  have bd: "B=D"
  proof (rule poly_mapping_eqI)
    fix v
    show "Poly_Mapping.lookup B v = Poly_Mapping.lookup D v"
    proof (cases "v=n")
      case True
      have nv: "\<not> v<n" using True by simp
      have az: "Poly_Mapping.lookup A v=0"
        by (rule roth_left_support_lookup_zero[OF a nv])
      have cz: "Poly_Mapping.lookup C v=0"
        by (rule roth_left_support_lookup_zero[OF c nv])
      show ?thesis using ev[of v] az cz by simp
    next
      case False
      have bz: "Poly_Mapping.lookup B v=0"
        by (rule roth_single_support_lookup_zero[OF b False])
      have dz: "Poly_Mapping.lookup D v=0"
        by (rule roth_single_support_lookup_zero[OF d False])
      show ?thesis using bz dz by simp
    qed
  qed
  show ?thesis using ac bd by simp
qed

lemma roth_hasse_nonzero_split_index:
  fixes \<mu> J K :: "(nat,nat) poly_mapping"
    and \<phi> \<psi> :: "rat mpoly"
  assumes mi: "Poly_Mapping.keys \<mu> \<subseteq> {..<n}"
    and pv: "vars \<phi> \<subseteq> {..<n}"
    and qv: "vars \<psi> \<subseteq> {n}"
    and jnz: "roth_hasse J \<phi> \<noteq> 0"
    and knz: "roth_hasse K \<psi> \<noteq> 0"
    and eq: "\<mu> + Poly_Mapping.single n j = J + K"
  shows "J = \<mu> \<and> K = Poly_Mapping.single n j"
proof -
  have Jv: "Poly_Mapping.keys J \<subseteq> {..<n}"
    using roth_hasse_index_vars[OF jnz] pv by auto
  have Kv: "Poly_Mapping.keys K \<subseteq> {n}"
    using roth_hasse_index_vars[OF knz] qv by auto
  have sv: "Poly_Mapping.keys (Poly_Mapping.single n j) \<subseteq> {n}"
    by (auto simp: in_keys_iff lookup_single when_def)
  show ?thesis
    using roth_split_index_unique[OF mi sv Jv Kv eq] by simp
qed

lemma roth_hasse_outer_unique:
  fixes \<mu> J :: "(nat,nat) poly_mapping"
    and \<phi> \<psi> :: "rat mpoly"
  assumes mi: "Poly_Mapping.keys \<mu> \<subseteq> {..<n}"
    and pv: "vars \<phi> \<subseteq> {..<n}"
    and qv: "vars \<psi> \<subseteq> {n}"
    and neq: "J \<noteq> \<mu>"
  shows "roth_hasse J \<phi> *
    (\<Sum>K. roth_hasse K \<psi> when
      \<mu> + Poly_Mapping.single n j = J + K) = 0"
proof (rule ccontr)
  assume nz: "\<not> roth_hasse J \<phi> *
    (\<Sum>K. roth_hasse K \<psi> when
      \<mu> + Poly_Mapping.single n j = J + K) = 0"
  have jnz: "roth_hasse J \<phi> \<noteq> 0" using nz by auto
  have snz: "(\<Sum>K. roth_hasse K \<psi> when
    \<mu> + Poly_Mapping.single n j = J + K) \<noteq> 0"
    using nz by auto
  obtain K where knz: "(roth_hasse K \<psi> when
    \<mu> + Poly_Mapping.single n j = J + K) \<noteq> 0"
    using Sum_any.not_neutral_obtains_not_neutral[OF snz] by blast
  have kz: "roth_hasse K \<psi> \<noteq> 0"
    and eq: "\<mu> + Poly_Mapping.single n j = J + K"
    using knz by (auto simp: when_def split: if_splits)
  have "J = \<mu>"
    using roth_hasse_nonzero_split_index[OF mi pv qv jnz kz eq] by simp
  then show False using neq by blast
qed

lemma roth_hasse_inner_collapse:
  "(\<Sum>K. roth_hasse K \<psi> when
      \<mu> + Poly_Mapping.single n j = \<mu> + K) =
    roth_hasse (Poly_Mapping.single n j) \<psi>"
  by simp

lemma roth_hasse_outer_point:
  fixes \<mu> J :: "(nat,nat) poly_mapping"
    and \<phi> \<psi> :: "rat mpoly"
  assumes mi: "Poly_Mapping.keys \<mu> \<subseteq> {..<n}"
    and pv: "vars \<phi> \<subseteq> {..<n}"
    and qv: "vars \<psi> \<subseteq> {n}"
  shows "roth_hasse J \<phi> *
    (\<Sum>K. roth_hasse K \<psi> when
      \<mu> + Poly_Mapping.single n j = J + K) =
    ((roth_hasse \<mu> \<phi> *
      (\<Sum>K. roth_hasse K \<psi> when
        \<mu> + Poly_Mapping.single n j = \<mu> + K))
      when (J = \<mu>))"
proof (cases "J = \<mu>")
  case True
  then show ?thesis by simp
next
  case False
  have z: "roth_hasse J \<phi> *
    (\<Sum>K. roth_hasse K \<psi> when
      \<mu> + Poly_Mapping.single n j = J + K) = 0"
    by (rule roth_hasse_outer_unique[OF mi pv qv False])
  show ?thesis using z False by (simp add: when_def)
qed

lemma roth_hasse_disjoint_product:
  fixes \<mu> :: "(nat,nat) poly_mapping"
    and \<phi> \<psi> :: "rat mpoly"
  assumes mi: "Poly_Mapping.keys \<mu> \<subseteq> {..<n}"
    and pv: "vars \<phi> \<subseteq> {..<n}"
    and qv: "vars \<psi> \<subseteq> {n}"
  shows "roth_hasse (\<mu> + Poly_Mapping.single n j) (\<phi> * \<psi>) =
    roth_hasse \<mu> \<phi> *
      roth_hasse (Poly_Mapping.single n j) \<psi>"
proof -
  have "roth_hasse (\<mu> + Poly_Mapping.single n j) (\<phi> * \<psi>) =
    (\<Sum>J. roth_hasse J \<phi> *
      (\<Sum>K. roth_hasse K \<psi> when
        \<mu> + Poly_Mapping.single n j = J + K))"
    by (rule roth_hasse_mult)
  also have "\<dots> =
    (\<Sum>J. ((roth_hasse \<mu> \<phi> *
      (\<Sum>K. roth_hasse K \<psi> when
        \<mu> + Poly_Mapping.single n j = \<mu> + K))
      when (J = \<mu>)))"
    by (rule Sum_any.cong)
      (rule roth_hasse_outer_point[OF mi pv qv])
  also have "\<dots> = roth_hasse \<mu> \<phi> *
    roth_hasse (Poly_Mapping.single n j) \<psi>"
    by (simp add: roth_hasse_inner_collapse)
  finally show ?thesis .
qed

end
