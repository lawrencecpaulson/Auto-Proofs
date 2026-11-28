theory MPoly_Taylor
  imports
    "Polynomials.More_MPoly_Type"
    "HOL-Library.FuncSet"
    "Polynomials.MPoly_PM"
    "HOL-Library.Extended_Real"
begin

section \<open>Finite boxes of multivariate exponents\<close>

definition pjet_exponent_box ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) set" where
  "pjet_exponent_box m r \<equiv>
    (\<lambda>f. Abs_poly_mapping (\<lambda>v. if v < m then f v else 0)) `
      (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"

lemma finite_pjet_exponent_box [simp]:
  "finite (pjet_exponent_box m r)"
  unfolding pjet_exponent_box_def by (intro finite_imageI finite_PiE) auto

lemma pjet_exponent_boxI:
  assumes vars: "Poly_Mapping.keys I \<subseteq> {..<m}"
    and bound: "\<And>v. v < m \<Longrightarrow> Poly_Mapping.lookup I v \<le> r v"
  shows "I \<in> pjet_exponent_box m r"
proof -
  let ?f = "restrict (Poly_Mapping.lookup I) {..<m}"
  have fmem: "?f \<in> (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
    using bound by (auto simp: PiE_def)
  have fin: "finite {v. (if v < m then ?f v else 0) \<noteq> 0}"
    by (rule finite_subset[of _ "{..<m}"]) auto
  have "I = Abs_poly_mapping (\<lambda>v. if v < m then ?f v else 0)"
    using fin keys.rep_eq subsetD vars by (intro Poly_Mapping.poly_mapping_eqI) fastforce
  then show ?thesis
    unfolding pjet_exponent_box_def
    using fmem by blast
qed

lemma pjet_exponent_boxD:
  assumes "I \<in> pjet_exponent_box m r"
  shows "Poly_Mapping.keys I \<subseteq> {..<m}"
    "\<And>v. v < m \<Longrightarrow> Poly_Mapping.lookup I v \<le> r v"
proof -
  obtain f where f:
    "f \<in> (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
    "I = Abs_poly_mapping (\<lambda>v. if v < m then f v else 0)"
    using assms by (auto simp: pjet_exponent_box_def)
  have fin: "finite {v. (if v < m then f v else 0) \<noteq> 0}"
    by (rule finite_subset[of _ "{..<m}"]) auto
  show "Poly_Mapping.keys I \<subseteq> {..<m}"
    using f fin by (auto simp: Poly_Mapping.keys.rep_eq)
  show "\<And>v. v < m \<Longrightarrow> Poly_Mapping.lookup I v \<le> r v"
    using f fin by (auto simp: PiE_def)
qed

lemma pjet_exponent_box_iff:
  "I \<in> pjet_exponent_box m r \<longleftrightarrow>
    Poly_Mapping.keys I \<subseteq> {..<m} \<and>
    (\<forall>v<m. Poly_Mapping.lookup I v \<le> r v)"
  using pjet_exponent_boxI pjet_exponent_boxD by blast

definition pjet_poly_in_box ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a::zero mpoly \<Rightarrow> bool" where
  "pjet_poly_in_box m r P \<equiv>
    Poly_Mapping.keys (mapping_of P) \<subseteq> pjet_exponent_box m r"

lemma pjet_poly_in_box_zero [simp]:
  "pjet_poly_in_box m r (0::'a::zero mpoly)"
  by (simp add: pjet_poly_in_box_def zero_mpoly.rep_eq)

lemma pjet_poly_in_box_monom:
  assumes "I \<in> pjet_exponent_box m r"
  shows "pjet_poly_in_box m r (monom I c)"
  using assms
  by (auto simp: pjet_poly_in_box_def mapping_of_monom keys_single)

lemma pjet_poly_in_box_add:
  assumes "pjet_poly_in_box m r P" "pjet_poly_in_box m r Q"
  shows "pjet_poly_in_box m r (P + Q)"
  using assms
  by (auto simp: pjet_poly_in_box_def plus_mpoly.rep_eq
    dest: subsetD[OF Poly_Mapping.keys_add])

lemma pjet_poly_in_box_sum:
  assumes "finite S" "\<And>x. x \<in> S \<Longrightarrow> pjet_poly_in_box m r (P x)"
  shows "pjet_poly_in_box m r (\<Sum>x\<in>S. P x)"
  using assms by (induction S rule: finite_induct) (simp_all add: pjet_poly_in_box_add)

lemma pjet_coeff_zero_outside_box:
  assumes "pjet_poly_in_box m r P" "I \<notin> pjet_exponent_box m r"
  shows "coeff P I = 0"
  using assms by (auto simp: pjet_poly_in_box_def coeff_def
    not_in_keys_iff_lookup_eq_zero)

lemma pjet_exponent_le_degree:
  fixes P :: "'a::zero mpoly"
  assumes "I \<in> Poly_Mapping.keys (mapping_of P)"
  shows "Poly_Mapping.lookup I v \<le> MPoly_Type.degree P v"
  using assms by (simp add: MPoly_Type.degree.rep_eq)

lemma pjet_degree_le_of_box:
  fixes P :: "'a::zero mpoly"
  assumes "pjet_poly_in_box m r P" "v < m"
  shows "MPoly_Type.degree P v \<le> r v"
  using assms unfolding pjet_poly_in_box_def MPoly_Type.degree.rep_eq
  by (auto simp: Max_le_iff pjet_exponent_box_iff)

lemma pjet_degree_outside_box:
  fixes P :: "'a::zero mpoly"
  assumes box: "pjet_poly_in_box m r P" and outside: "m \<le> v"
  shows "MPoly_Type.degree P v = 0"
proof -
  have all_zero: "Poly_Mapping.lookup I v = 0"
    if "I \<in> Poly_Mapping.keys (mapping_of P)" for I
  proof -
    have "I \<in> pjet_exponent_box m r"
      using box that by (auto simp: pjet_poly_in_box_def)
    then have "v \<notin> Poly_Mapping.keys I"
      using pjet_exponent_boxD outside by fastforce
    then show ?thesis
      by (simp add: not_in_keys_iff_lookup_eq_zero)
  qed
  have set_eq: "insert 0 ((\<lambda>I. Poly_Mapping.lookup I v) `
      Poly_Mapping.keys (mapping_of P)) = {0}"
    using all_zero by auto
  then show ?thesis
    by (simp add: set_eq degree.rep_eq)
qed

lemma pjet_poly_in_box_iff_degree:
  fixes P :: "'a::zero mpoly"
  shows "pjet_poly_in_box m r P \<longleftrightarrow>
    (\<forall>v<m. MPoly_Type.degree P v \<le> r v) \<and>
    (\<forall>v\<ge>m. MPoly_Type.degree P v = 0)"
proof
  assume "pjet_poly_in_box m r P"
  then show "(\<forall>v<m. MPoly_Type.degree P v \<le> r v) \<and> (\<forall>v\<ge>m. MPoly_Type.degree P v = 0)"
    using pjet_degree_le_of_box pjet_degree_outside_box by blast
next
  assume degrees: "(\<forall>v<m. MPoly_Type.degree P v \<le> r v) \<and>
    (\<forall>v\<ge>m. MPoly_Type.degree P v = 0)"
  have in_box: "I \<in> pjet_exponent_box m r"
    if I: "I \<in> Poly_Mapping.keys (mapping_of P)" for I
  proof (rule pjet_exponent_boxI)
    show "Poly_Mapping.keys I \<subseteq> {..<m}"
    proof
      fix v
      assume v: "v \<in> Poly_Mapping.keys I"
      show "v \<in> {..<m}"
      proof (rule ccontr)
        assume "v \<notin> {..<m}"
        then have "Poly_Mapping.lookup I v = 0"
          using degrees pjet_exponent_le_degree[OF I, where v = v] by simp
        then show False
          using v lookup_eq_zero_in_keys_contradict by blast
      qed
    qed
    fix v
    assume v: "v < m"
    then show "Poly_Mapping.lookup I v \<le> r v"
      by (meson le_trans pjet_exponent_le_degree degrees that)
  qed
  show "pjet_poly_in_box m r P"
    using in_box by (auto simp: pjet_poly_in_box_def)
qed

section \<open>Multivariate polynomial translation\<close>

definition pjet_mpoly_subst ::
  "(nat \<Rightarrow> 'a::comm_ring_1 mpoly) \<Rightarrow> 'a mpoly \<Rightarrow> 'a mpoly" where
  "pjet_mpoly_subst f P \<equiv>
    MPoly (MPoly_PM.poly_subst (\<lambda>v. mapping_of (f v)) (mapping_of P))"

lemma mapping_of_pjet_mpoly_subst [simp]:
  "mapping_of (pjet_mpoly_subst f P) = MPoly_PM.poly_subst (\<lambda>v. mapping_of (f v)) (mapping_of P)"
  by (simp add: pjet_mpoly_subst_def MPoly_inverse)

lemma pjet_mpoly_subst_add:
  "pjet_mpoly_subst f (P + Q) = pjet_mpoly_subst f P + pjet_mpoly_subst f Q"
  by (simp add: mapping_of_inject[symmetric] plus_mpoly.rep_eq
    MPoly_PM.poly_subst_plus)

lemma pjet_mpoly_subst_zero [simp]:
  "pjet_mpoly_subst f 0 = 0"
  by (simp add: mapping_of_inject[symmetric] zero_mpoly.rep_eq)

lemma pjet_mpoly_subst_sum:
  assumes "finite S"
  shows "pjet_mpoly_subst f (sum P S) = (\<Sum>x\<in>S. pjet_mpoly_subst f (P x))"
  by (simp add: fun_sum_commute_canc pjet_mpoly_subst_add)

lemma pjet_mpoly_subst_mult:
  "pjet_mpoly_subst f (P * Q) = pjet_mpoly_subst f P * pjet_mpoly_subst f Q"
  by (simp add: mapping_of_inject[symmetric] times_mpoly.rep_eq
    MPoly_PM.poly_subst_times)

lemma pjet_mpoly_subst_comp:
  "pjet_mpoly_subst f (pjet_mpoly_subst g P) =
    pjet_mpoly_subst (\<lambda>v. pjet_mpoly_subst f (g v)) P"
  by (simp add: mapping_of_inject[symmetric] MPoly_PM.poly_subst_poly_subst)

lemma pjet_mpoly_subst_Var [simp]:
  "pjet_mpoly_subst f (Var v) = f v"
  by (simp add: mapping_of_inject[symmetric] Var.rep_eq
    Var\<^sub>0_def MPoly_PM.poly_subst_monomial MPoly_PM.subst_pp_single)

lemma pjet_mpoly_subst_Const [simp]:
  "pjet_mpoly_subst f (Const c) = Const c"
  by (simp add: mapping_of_inject[symmetric] Const.rep_eq
    Const\<^sub>0_def MPoly_PM.poly_subst_monomial MPoly_PM.subst_pp_def
    punit.monom_mult_monomial single_one[symmetric] del: single_one)

lemma pjet_mpoly_subst_id [simp]: "pjet_mpoly_subst Var P = P"
  by (simp add: mapping_of_inject[symmetric] MPoly_PM.poly_subst_id
    Var.rep_eq Var\<^sub>0_def)

lemma pjet_Const_add: "Const (a + b) = Const a + Const b"
  by (simp add: mapping_of_inject[symmetric] Const.rep_eq
    Const\<^sub>0_def plus_mpoly.rep_eq single_add)

lemma pjet_Const_zero [simp]: "Const 0 = 0"
  by (simp add: mapping_of_inject[symmetric] Const.rep_eq
    Const\<^sub>0_zero zero_mpoly.rep_eq)

lemma pjet_Const_uminus: "Const (- a) = - Const a"
  by (simp add: mapping_of_inject[symmetric] Const.rep_eq
    Const\<^sub>0_minus uminus_mpoly.rep_eq)

definition pjet_translate ::
  "(nat \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> 'a mpoly \<Rightarrow> 'a mpoly" where
  "pjet_translate a P \<equiv> pjet_mpoly_subst (\<lambda>v. Var v + Const (a v)) P"

lemma pjet_translate_comp:
  "pjet_translate a (pjet_translate b P) =
    pjet_translate (\<lambda>v. a v + b v) P"
  by (simp add: pjet_translate_def pjet_mpoly_subst_comp
    pjet_mpoly_subst_add pjet_Const_add[symmetric] algebra_simps)

lemma pjet_translate_add:
  "pjet_translate a (P + Q) = pjet_translate a P + pjet_translate a Q"
  by (simp add: pjet_translate_def pjet_mpoly_subst_add)

lemma pjet_translate_mult:
  "pjet_translate a (P * Q) = pjet_translate a P * pjet_translate a Q"
  by (simp add: pjet_translate_def pjet_mpoly_subst_mult)

lemma pjet_translate_zero [simp]:
  "pjet_translate (\<lambda>_. 0) P = P"
  by (simp add: pjet_translate_def)

lemma pjet_translate_inverse:
  "pjet_translate (\<lambda>v. - a v) (pjet_translate a P) = P"
  by (simp add: pjet_translate_comp)

lemma pjet_vars_mapping:
  "vars P = MPoly_PM.indets (mapping_of P)"
  by (simp add: vars_def MPoly_PM.indets_def)

lemma pjet_vars_Var:
  "vars (Var v :: 'a::comm_ring_1 mpoly) \<subseteq> {v}"
  by (simp add: pjet_vars_mapping Var.rep_eq Var\<^sub>0_def
    MPoly_PM.indets_monomial_single_subset)

lemma pjet_vars_Const:
  "vars (Const c :: 'a::comm_ring_1 mpoly) = {}"
  by (simp add: pjet_vars_mapping Const.rep_eq Const\<^sub>0_def)

lemma pjet_vars_shift:
  "vars (Var v + Const c :: 'a::comm_ring_1 mpoly) \<subseteq> {v}"
  using vars_add pjet_vars_Var pjet_vars_Const by blast

lemma pjet_vars_translate_subset:
  "vars (pjet_translate a P) \<subseteq> vars P"
  using pjet_vars_shift
  by (auto simp: pjet_vars_mapping pjet_translate_def elim!: MPoly_PM.in_indets_poly_substE)

lemma pjet_vars_translate:
  "vars (pjet_translate a P) = vars P"
  by (metis pjet_translate_inverse pjet_vars_translate_subset order_antisym)

lemma pjet_mapping_of_sum:
  assumes "finite S"
  shows "mapping_of (sum f S) = (\<Sum>x\<in>S. mapping_of (f x))"
  using assms fun_sum_commute plus_mpoly.rep_eq zero_mpoly.rep_eq by blast

lemma pjet_mapping_of_prod:
  assumes "finite S"
  shows "mapping_of (prod f S) = (\<Prod>x\<in>S. mapping_of (f x))"
  using fun_prod_commute one_mpoly.rep_eq times_mpoly.rep_eq by blast

lemma pjet_mapping_of_power:
  "mapping_of (P ^ n) = mapping_of P ^ n"
  by (induction n) (simp_all add: one_mpoly.rep_eq times_mpoly.rep_eq)

lemma pjet_mpoly_subst_monom:
  "pjet_mpoly_subst f (monom I c) =
    Const c * (\<Prod>v\<in>Poly_Mapping.keys I. f v ^ Poly_Mapping.lookup I v)"
  by (simp add: mapping_of_inject[symmetric]
    MPoly_PM.poly_subst_monomial MPoly_PM.subst_pp_def
    pjet_mapping_of_prod pjet_mapping_of_power times_mpoly.rep_eq
    Const.rep_eq Const\<^sub>0_def times_monomial_left[symmetric])

lemma pjet_sum_monom:
  "P = (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P). monom I (coeff P I))"
  by (simp add: mapping_of_inject[symmetric] coeff_def
    pjet_mapping_of_sum poly_mapping_sum_monomials)

definition pjet_taylor_coeff ::
  "[nat \<Rightarrow> 'a::comm_ring_1, nat \<Rightarrow>\<^sub>0 nat, 'a mpoly] \<Rightarrow> 'a"
    where "pjet_taylor_coeff a I P \<equiv> coeff (pjet_translate a P) I"

lemma pjet_taylor_coeff_key:
  "pjet_taylor_coeff a I P \<noteq> 0 \<longleftrightarrow>
    I \<in> Poly_Mapping.keys (mapping_of (pjet_translate a P))"
  by (simp add: pjet_taylor_coeff_def coeff_def in_keys_iff)

lemma pjet_taylor_coeff_add:
  "pjet_taylor_coeff a I (P + Q) = pjet_taylor_coeff a I P + pjet_taylor_coeff a I Q"
  by (simp add: pjet_taylor_coeff_def pjet_translate_add coeff_add)

lemma pjet_taylor_coeff_translate:
  "pjet_taylor_coeff a I (pjet_translate b P) = pjet_taylor_coeff (\<lambda>v. a v + b v) I P"
  by (simp add: pjet_taylor_coeff_def pjet_translate_comp)

lemma pjet_taylor_coeff_mult:
  "pjet_taylor_coeff a I (P * Q) =
    (\<Sum>J. pjet_taylor_coeff a J P *
      (\<Sum>K. pjet_taylor_coeff a K Q when I = J + K))"
  by (simp add: pjet_taylor_coeff_def pjet_translate_mult
    coeff_def times_mpoly.rep_eq lookup_mult)

lemma pjet_taylor_coeff_mult_support:
  assumes "pjet_taylor_coeff a I (P * Q) \<noteq> 0"
  obtains J K where
    "pjet_taylor_coeff a J P \<noteq> 0" "pjet_taylor_coeff a K Q \<noteq> 0" "I = J + K"
  using assms
  by (metis pjet_taylor_coeff_def pjet_translate_mult coeff_def
    in_keys_iff in_keys_timesE times_mpoly.rep_eq)

lemma pjet_taylor_coeff_all_zero:
  "(\<forall>I. pjet_taylor_coeff a I P = 0) \<longleftrightarrow> P = 0"
proof
  assume h: "\<forall>I. pjet_taylor_coeff a I P = 0"
  then show "P = 0"
    using pjet_translate_inverse[of a P] coeff_all_0
    by (force simp: pjet_taylor_coeff_def pjet_translate_def)
next
  assume "P = 0"
  then show "\<forall>I. pjet_taylor_coeff a I P = 0"
    by (metis add_cancel_left_right pjet_taylor_coeff_add)
qed

lemma pjet_taylor_identity:
  "P = (\<Sum>I\<in>Poly_Mapping.keys (mapping_of (pjet_translate a P)).
    pjet_translate (\<lambda>v. - a v) (monom I (pjet_taylor_coeff a I P)))"
  unfolding pjet_taylor_coeff_def
  using pjet_translate_inverse[symmetric, of P a] pjet_sum_monom
  by (metis (mono_tags, lifting) finite_keys pjet_mpoly_subst_sum
      pjet_translate_def sum.cong)

lemma pjet_taylor_identity_explicit:
  "P = (\<Sum>I\<in>Poly_Mapping.keys (mapping_of (pjet_translate a P)).
    Const (pjet_taylor_coeff a I P) *
      (\<Prod>v\<in>Poly_Mapping.keys I. (Var v - Const (a v)) ^ Poly_Mapping.lookup I v))"
  by (subst pjet_taylor_identity[of P a])
     (simp add: pjet_translate_def pjet_mpoly_subst_monom
      pjet_Const_uminus)

section \<open>Products in disjoint sets of variables\<close>

lemma pjet_lookup_zero_outside:
  assumes "Poly_Mapping.keys I \<subseteq> A" "v \<notin> A"
  shows "Poly_Mapping.lookup I v = 0"
  using assms by (metis not_in_keys_iff_lookup_eq_zero subsetD)

lemma pjet_disjoint_exponent_left:
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
  have "Poly_Mapping.lookup I v + Poly_Mapping.lookup J v =
    Poly_Mapping.lookup I2 v + Poly_Mapping.lookup J2 v"
    using eq by (metis lookup_add)
  with assms show "Poly_Mapping.lookup I v = Poly_Mapping.lookup I2 v"
    by (metis Nat.add_0_right disjoint_iff pjet_lookup_zero_outside)
qed

lemma pjet_disjoint_exponent_unique:
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
    by (rule pjet_disjoint_exponent_left[OF assms])
  with eq have j: "J = J2"
    by auto
  show ?thesis using i j by simp
qed

lemma pjet_select_lookup:
  fixes P :: "'k \<Rightarrow>\<^sub>0 'a::comm_monoid_add"
  shows "(\<Sum>x\<in>Poly_Mapping.keys P \<inter> {I}. Poly_Mapping.lookup P x) = Poly_Mapping.lookup P I"
  by (cases "I \<in> Poly_Mapping.keys P")
    (simp_all add: not_in_keys_iff_lookup_eq_zero)

lemma pjet_disjoint_prod_coeff_ambient:
  fixes P Q :: "'a::idom mpoly"
  assumes "vars P \<subseteq> A"
    and "vars Q \<subseteq> B"
    and "Poly_Mapping.keys I \<subseteq> A"
    and "Poly_Mapping.keys J \<subseteq> B"
    and "A \<inter> B = {}"
  shows "coeff (P * Q) (I + J) = coeff P I * coeff Q J"
proof -
  have uniq: "I + J = I2 + J2 \<longleftrightarrow> I = I2 \<and> J = J2"
    if i2: "I2 \<in> Poly_Mapping.keys (mapping_of P)"
      and j2: "J2 \<in> Poly_Mapping.keys (mapping_of Q)"
    for I2 J2
    using pjet_disjoint_exponent_unique [of I A I2 J B J2] assms that
    by (auto simp: vars_def)
  have inner:
    "(\<Sum>v\<in>Poly_Mapping.keys (mapping_of Q).
      Poly_Mapping.lookup (mapping_of Q) v when I + J = t + v) =
      (if t = I then coeff Q J else 0)"
    if t: "t \<in> Poly_Mapping.keys (mapping_of P)" for t
    using uniq[OF t]
    by (simp add: when_def coeff_def sum.If_cases pjet_select_lookup)
  then show ?thesis
    unfolding coeff_def times_mpoly.rep_eq lookup_times
    by (simp add: inner sum.If_cases if_distrib coeff_def
      pjet_select_lookup flip: sum_distrib_right)
qed

lemma pjet_disjoint_prod_coeff:
  fixes P Q :: "'a::idom mpoly"
  assumes "vars P \<inter> vars Q = {}"
    and "I \<in> Poly_Mapping.keys (mapping_of P)"
    and "J \<in> Poly_Mapping.keys (mapping_of Q)"
  shows "coeff (P * Q) (I + J) = coeff P I * coeff Q J"
  using assms
  by (intro pjet_disjoint_prod_coeff_ambient) (auto simp: vars_def)

lemma pjet_disjoint_taylor_coeff:
  fixes P Q :: "'a::idom mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
    and i: "pjet_taylor_coeff a I P \<noteq> 0"
    and j: "pjet_taylor_coeff a J Q \<noteq> 0"
  shows "pjet_taylor_coeff a (I + J) (P * Q) = pjet_taylor_coeff a I P * pjet_taylor_coeff a J Q"
  using assms pjet_disjoint_prod_coeff [of "pjet_translate a P" "pjet_translate a Q" I J]
  by (simp add: pjet_taylor_coeff_def pjet_translate_mult
    pjet_vars_translate coeff_def in_keys_iff)


end
