theory Disjoint_Index
  imports
    "Polynomials.More_MPoly_Type"
    "HOL-Library.FuncSet"
    "Polynomials.MPoly_PM"
    "HOL-Library.Extended_Real"
begin

section \<open>Finite boxes of multivariate exponents\<close>

definition roth_exponent_box ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) set" where
  "roth_exponent_box m r =
    (\<lambda>f. Abs_poly_mapping (\<lambda>v. if v < m then f v else 0)) `
      (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"

lemma finite_roth_exponent_box [simp]:
  "finite (roth_exponent_box m r)"
  unfolding roth_exponent_box_def by (intro finite_imageI finite_PiE) auto

lemma roth_exponent_boxI:
  assumes vars: "Poly_Mapping.keys I \<subseteq> {..<m}"
    and bound: "\<And>v. v < m \<Longrightarrow> Poly_Mapping.lookup I v \<le> r v"
  shows "I \<in> roth_exponent_box m r"
proof -
  let ?f = "restrict (Poly_Mapping.lookup I) {..<m}"
  have fmem: "?f \<in> (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
    using bound by (auto simp: PiE_def)
  have fin: "finite {v. (if v < m then ?f v else 0) \<noteq> 0}"
    by (rule finite_subset[of _ "{..<m}"]) auto
  have "Abs_poly_mapping (\<lambda>v. if v < m then ?f v else 0) = I"
  proof (rule Poly_Mapping.poly_mapping_eqI)
    fix v
    show "Poly_Mapping.lookup
        (Abs_poly_mapping (\<lambda>v. if v < m then ?f v else 0)) v =
        Poly_Mapping.lookup I v"
    proof (cases "v < m")
      case True
      then show ?thesis
        using fin by simp
    next
      case False
      then have "v \<notin> Poly_Mapping.keys I"
        using vars by auto
      then show ?thesis
        using fin False by (simp add: not_in_keys_iff_lookup_eq_zero)
    qed
  qed
  then have eq: "I = Abs_poly_mapping (\<lambda>v. if v < m then ?f v else 0)"
    by simp
  show ?thesis
    unfolding roth_exponent_box_def
  proof (rule image_eqI[where x = ?f])
    show "I = Abs_poly_mapping (\<lambda>v. if v < m then ?f v else 0)"
      by (rule eq)
    show "?f \<in> (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
      by (rule fmem)
  qed
qed

lemma roth_exponent_boxD:
  assumes "I \<in> roth_exponent_box m r"
  shows "Poly_Mapping.keys I \<subseteq> {..<m}"
    "\<And>v. v < m \<Longrightarrow> Poly_Mapping.lookup I v \<le> r v"
proof -
  obtain f where f:
    "f \<in> (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
    "I = Abs_poly_mapping (\<lambda>v. if v < m then f v else 0)"
    using assms by (auto simp: roth_exponent_box_def)
  have fin: "finite {v. (if v < m then f v else 0) \<noteq> 0}"
    by (rule finite_subset[of _ "{..<m}"]) auto
  show "Poly_Mapping.keys I \<subseteq> {..<m}"
    using f fin by (auto simp: Poly_Mapping.keys.rep_eq)
  show "\<And>v. v < m \<Longrightarrow> Poly_Mapping.lookup I v \<le> r v"
    using f fin by (auto simp: PiE_def)
qed

lemma roth_exponent_box_iff:
  "I \<in> roth_exponent_box m r \<longleftrightarrow>
    Poly_Mapping.keys I \<subseteq> {..<m} \<and>
    (\<forall>v<m. Poly_Mapping.lookup I v \<le> r v)"
  using roth_exponent_boxI roth_exponent_boxD by blast

definition roth_poly_in_box ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a::zero mpoly \<Rightarrow> bool" where
  "roth_poly_in_box m r P \<longleftrightarrow>
    Poly_Mapping.keys (mapping_of P) \<subseteq> roth_exponent_box m r"

lemma roth_poly_in_box_zero [simp]:
  "roth_poly_in_box m r (0::'a::zero mpoly)"
  by (simp add: roth_poly_in_box_def zero_mpoly.rep_eq)

lemma roth_poly_in_box_monom:
  assumes "I \<in> roth_exponent_box m r"
  shows "roth_poly_in_box m r (monom I c)"
  using assms
  by (auto simp: roth_poly_in_box_def mapping_of_monom keys_single)

lemma roth_poly_in_box_add:
  assumes "roth_poly_in_box m r P" "roth_poly_in_box m r Q"
  shows "roth_poly_in_box m r (P + Q)"
  using assms
  by (auto simp: roth_poly_in_box_def plus_mpoly.rep_eq
    dest: subsetD[OF Poly_Mapping.keys_add])

lemma roth_poly_in_box_sum:
  assumes "finite S" "\<And>x. x \<in> S \<Longrightarrow> roth_poly_in_box m r (P x)"
  shows "roth_poly_in_box m r (\<Sum>x\<in>S. P x)"
  using assms by (induction S rule: finite_induct)
    (simp_all add: roth_poly_in_box_add)

lemma roth_coeff_zero_outside_box:
  assumes "roth_poly_in_box m r P" "I \<notin> roth_exponent_box m r"
  shows "coeff P I = 0"
  using assms by (auto simp: roth_poly_in_box_def coeff_def
    not_in_keys_iff_lookup_eq_zero)

lemma roth_exponent_le_degree:
  fixes P :: "'a::zero mpoly"
  assumes "I \<in> Poly_Mapping.keys (mapping_of P)"
  shows "Poly_Mapping.lookup I v \<le> MPoly_Type.degree P v"
  using assms by (simp add: MPoly_Type.degree.rep_eq)

lemma roth_degree_le_of_box:
  fixes P :: "'a::zero mpoly"
  assumes "roth_poly_in_box m r P" "v < m"
  shows "MPoly_Type.degree P v \<le> r v"
  using assms unfolding roth_poly_in_box_def MPoly_Type.degree.rep_eq
  by (auto simp: Max_le_iff roth_exponent_box_iff)

lemma roth_degree_outside_box:
  fixes P :: "'a::zero mpoly"
  assumes box: "roth_poly_in_box m r P" and outside: "m \<le> v"
  shows "MPoly_Type.degree P v = 0"
proof -
  have all_zero: "Poly_Mapping.lookup I v = 0"
    if "I \<in> Poly_Mapping.keys (mapping_of P)" for I
  proof -
    have "I \<in> roth_exponent_box m r"
      using box that by (auto simp: roth_poly_in_box_def)
    then have "Poly_Mapping.keys I \<subseteq> {..<m}"
      by (rule roth_exponent_boxD(1))
    then have "v \<notin> Poly_Mapping.keys I"
      using outside by auto
    then show ?thesis
      by (simp add: not_in_keys_iff_lookup_eq_zero)
  qed
  have set_eq: "insert 0 ((\<lambda>I. Poly_Mapping.lookup I v) `
      Poly_Mapping.keys (mapping_of P)) = {0}"
    using all_zero by auto
  have "MPoly_Type.degree P v = Max {0}"
    by (simp only: MPoly_Type.degree.rep_eq set_eq)
  then show ?thesis
    by simp
qed

lemma roth_poly_in_box_iff_degree:
  fixes P :: "'a::zero mpoly"
  shows "roth_poly_in_box m r P \<longleftrightarrow>
    (\<forall>v<m. MPoly_Type.degree P v \<le> r v) \<and>
    (\<forall>v\<ge>m. MPoly_Type.degree P v = 0)"
proof
  assume "roth_poly_in_box m r P"
  then show "(\<forall>v<m. MPoly_Type.degree P v \<le> r v) \<and>
    (\<forall>v\<ge>m. MPoly_Type.degree P v = 0)"
    using roth_degree_le_of_box roth_degree_outside_box by blast
next
  assume degrees: "(\<forall>v<m. MPoly_Type.degree P v \<le> r v) \<and>
    (\<forall>v\<ge>m. MPoly_Type.degree P v = 0)"
  have in_box: "I \<in> roth_exponent_box m r"
    if I: "I \<in> Poly_Mapping.keys (mapping_of P)" for I
  proof (rule roth_exponent_boxI)
    show "Poly_Mapping.keys I \<subseteq> {..<m}"
    proof
      fix v
      assume v: "v \<in> Poly_Mapping.keys I"
      show "v \<in> {..<m}"
      proof (rule ccontr)
        assume "v \<notin> {..<m}"
        then have "MPoly_Type.degree P v = 0"
          using degrees by simp
        then have "Poly_Mapping.lookup I v = 0"
          using roth_exponent_le_degree[OF I, where v = v] by simp
        then have "v \<notin> Poly_Mapping.keys I"
          by (rule lookup_eq_zero_in_keys_contradict)
        then show False
          using v by simp
      qed
    qed
    fix v
    assume v: "v < m"
    have "Poly_Mapping.lookup I v \<le> MPoly_Type.degree P v"
      by (rule roth_exponent_le_degree[OF I])
    also have "\<dots> \<le> r v"
      using degrees v by simp
    finally show "Poly_Mapping.lookup I v \<le> r v" .
  qed
  show "roth_poly_in_box m r P"
    using in_box by (auto simp: roth_poly_in_box_def)
qed

section \<open>Multivariate polynomial translation\<close>

definition roth_mpoly_subst ::
  "(nat \<Rightarrow> 'a::comm_ring_1 mpoly) \<Rightarrow> 'a mpoly \<Rightarrow> 'a mpoly" where
  "roth_mpoly_subst f P =
    MPoly (MPoly_PM.poly_subst (\<lambda>v. mapping_of (f v)) (mapping_of P))"

lemma mapping_of_roth_mpoly_subst [simp]:
  "mapping_of (roth_mpoly_subst f P) =
    MPoly_PM.poly_subst (\<lambda>v. mapping_of (f v)) (mapping_of P)"
  by (simp add: roth_mpoly_subst_def MPoly_inverse)

lemma roth_mpoly_subst_add:
  "roth_mpoly_subst f (P + Q) =
    roth_mpoly_subst f P + roth_mpoly_subst f Q"
  by (simp add: mapping_of_inject[symmetric] plus_mpoly.rep_eq
    MPoly_PM.poly_subst_plus)

lemma roth_mpoly_subst_zero [simp]:
  "roth_mpoly_subst f 0 = 0"
  by (simp add: mapping_of_inject[symmetric] zero_mpoly.rep_eq)

lemma roth_mpoly_subst_sum:
  assumes "finite S"
  shows "roth_mpoly_subst f (sum P S) =
    (\<Sum>x\<in>S. roth_mpoly_subst f (P x))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: roth_mpoly_subst_add)

lemma roth_mpoly_subst_mult:
  "roth_mpoly_subst f (P * Q) =
    roth_mpoly_subst f P * roth_mpoly_subst f Q"
  by (simp add: mapping_of_inject[symmetric] times_mpoly.rep_eq
    MPoly_PM.poly_subst_times)

lemma roth_mpoly_subst_comp:
  "roth_mpoly_subst f (roth_mpoly_subst g P) =
    roth_mpoly_subst (\<lambda>v. roth_mpoly_subst f (g v)) P"
  by (simp add: mapping_of_inject[symmetric]
    MPoly_PM.poly_subst_poly_subst)

lemma roth_mpoly_subst_Var [simp]:
  "roth_mpoly_subst f (Var v) = f v"
  by (simp add: mapping_of_inject[symmetric] Var.rep_eq
    Var\<^sub>0_def MPoly_PM.poly_subst_monomial MPoly_PM.subst_pp_single)

lemma roth_mpoly_subst_Const [simp]:
  "roth_mpoly_subst f (Const c) = Const c"
  by (simp add: mapping_of_inject[symmetric] Const.rep_eq
    Const\<^sub>0_def MPoly_PM.poly_subst_monomial MPoly_PM.subst_pp_def
    punit.monom_mult_monomial single_one[symmetric] del: single_one)

lemma roth_mpoly_subst_id [simp]:
  "roth_mpoly_subst Var P = P"
  by (simp add: mapping_of_inject[symmetric] MPoly_PM.poly_subst_id
    Var.rep_eq Var\<^sub>0_def)

lemma roth_Const_add:
  "Const (a + b) = Const a + Const b"
  by (simp add: mapping_of_inject[symmetric] Const.rep_eq
    Const\<^sub>0_def plus_mpoly.rep_eq single_add)

lemma roth_Const_zero [simp]:
  "Const (0::'a::zero) = 0"
  by (simp add: mapping_of_inject[symmetric] Const.rep_eq
    Const\<^sub>0_zero zero_mpoly.rep_eq)

lemma roth_Const_uminus:
  "Const (- a) = - Const a"
  by (simp add: mapping_of_inject[symmetric] Const.rep_eq
    Const\<^sub>0_minus uminus_mpoly.rep_eq)

definition roth_translate ::
  "(nat \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> 'a mpoly \<Rightarrow> 'a mpoly" where
  "roth_translate a P =
    roth_mpoly_subst (\<lambda>v. Var v + Const (a v)) P"

lemma roth_translate_comp:
  "roth_translate a (roth_translate b P) =
    roth_translate (\<lambda>v. a v + b v) P"
  by (simp add: roth_translate_def roth_mpoly_subst_comp
    roth_mpoly_subst_add roth_Const_add[symmetric] algebra_simps)

lemma roth_translate_add:
  "roth_translate a (P + Q) = roth_translate a P + roth_translate a Q"
  by (simp add: roth_translate_def roth_mpoly_subst_add)

lemma roth_translate_mult:
  "roth_translate a (P * Q) = roth_translate a P * roth_translate a Q"
  by (simp add: roth_translate_def roth_mpoly_subst_mult)

lemma roth_translate_zero [simp]:
  "roth_translate (\<lambda>_. 0) P = P"
  by (simp add: roth_translate_def)

lemma roth_translate_inverse:
  "roth_translate (\<lambda>v. - a v) (roth_translate a P) = P"
  by (simp add: roth_translate_comp)

lemma roth_vars_mapping:
  "vars P = MPoly_PM.indets (mapping_of P)"
  by (simp add: vars_def MPoly_PM.indets_def)

lemma roth_vars_Var:
  "vars (Var v :: 'a::comm_ring_1 mpoly) \<subseteq> {v}"
  by (simp add: roth_vars_mapping Var.rep_eq Var\<^sub>0_def
    MPoly_PM.indets_monomial_single_subset)

lemma roth_vars_Const:
  "vars (Const c :: 'a::comm_ring_1 mpoly) = {}"
  by (simp add: roth_vars_mapping Const.rep_eq Const\<^sub>0_def)

lemma roth_vars_shift:
  "vars (Var v + Const c :: 'a::comm_ring_1 mpoly) \<subseteq> {v}"
  using vars_add roth_vars_Var roth_vars_Const by blast

lemma roth_vars_translate_subset:
  "vars (roth_translate a P) \<subseteq> vars P"
  using roth_vars_shift
  by (auto simp: roth_vars_mapping roth_translate_def
    elim!: MPoly_PM.in_indets_poly_substE)

lemma roth_vars_translate:
  "vars (roth_translate a P) = vars P"
  by (metis roth_translate_inverse roth_vars_translate_subset order_antisym)

lemma roth_mapping_of_sum:
  assumes "finite S"
  shows "mapping_of (sum f S) = (\<Sum>x\<in>S. mapping_of (f x))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: zero_mpoly.rep_eq plus_mpoly.rep_eq)

lemma roth_mapping_of_prod:
  assumes "finite S"
  shows "mapping_of (prod f S) = (\<Prod>x\<in>S. mapping_of (f x))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: one_mpoly.rep_eq times_mpoly.rep_eq)

lemma roth_mapping_of_power:
  "mapping_of (P ^ n) = mapping_of P ^ n"
  by (induction n) (simp_all add: one_mpoly.rep_eq times_mpoly.rep_eq)

lemma roth_mpoly_subst_monom:
  "roth_mpoly_subst f (monom I c) =
    Const c * (\<Prod>v\<in>Poly_Mapping.keys I.
      f v ^ Poly_Mapping.lookup I v)"
  by (simp add: mapping_of_inject[symmetric]
    MPoly_PM.poly_subst_monomial MPoly_PM.subst_pp_def
    roth_mapping_of_prod roth_mapping_of_power times_mpoly.rep_eq
    Const.rep_eq Const\<^sub>0_def times_monomial_left[symmetric])

lemma roth_sum_monom:
  "P = (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P). monom I (coeff P I))"
  by (simp add: mapping_of_inject[symmetric] coeff_def
    roth_mapping_of_sum poly_mapping_sum_monomials)

definition roth_taylor_coeff ::
  "(nat \<Rightarrow> 'a::comm_ring_1) \<Rightarrow>
    (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a mpoly \<Rightarrow> 'a" where
  "roth_taylor_coeff a I P = coeff (roth_translate a P) I"

lemma roth_taylor_coeff_key:
  "roth_taylor_coeff a I P \<noteq> 0 \<longleftrightarrow>
    I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))"
  by (simp add: roth_taylor_coeff_def coeff_def in_keys_iff)

lemma roth_taylor_coeff_add:
  "roth_taylor_coeff a I (P + Q) =
    roth_taylor_coeff a I P + roth_taylor_coeff a I Q"
  by (simp add: roth_taylor_coeff_def roth_translate_add
    coeff_add[symmetric])

lemma roth_taylor_coeff_translate:
  "roth_taylor_coeff a I (roth_translate b P) =
    roth_taylor_coeff (\<lambda>v. a v + b v) I P"
  by (simp add: roth_taylor_coeff_def roth_translate_comp)

lemma roth_taylor_coeff_mult:
  "roth_taylor_coeff a I (P * Q) =
    (\<Sum>J. roth_taylor_coeff a J P *
      (\<Sum>K. roth_taylor_coeff a K Q when I = J + K))"
  by (simp add: roth_taylor_coeff_def roth_translate_mult
    coeff_def times_mpoly.rep_eq lookup_mult)

lemma roth_taylor_coeff_mult_support:
  assumes "roth_taylor_coeff a I (P * Q) \<noteq> 0"
  obtains J K where
    "roth_taylor_coeff a J P \<noteq> 0"
    "roth_taylor_coeff a K Q \<noteq> 0"
    "I = J + K"
  using assms
  by (metis roth_taylor_coeff_def roth_translate_mult coeff_def
    in_keys_iff in_keys_timesE times_mpoly.rep_eq)

lemma roth_taylor_coeff_all_zero:
  "(\<forall>I. roth_taylor_coeff a I P = 0) \<longleftrightarrow> P = 0"
proof
  assume h: "\<forall>I. roth_taylor_coeff a I P = 0"
  have "roth_translate a P = 0"
    using h by (simp add: roth_taylor_coeff_def coeff_all_0)
  then show "P = 0"
    using roth_translate_inverse[of a P]
    by (simp add: roth_translate_def)
next
  assume "P = 0"
  then show "\<forall>I. roth_taylor_coeff a I P = 0"
    by (simp add: roth_taylor_coeff_def roth_translate_def
      coeff_def zero_mpoly.rep_eq)
qed

lemma roth_taylor_identity:
  "P = (\<Sum>I\<in>Poly_Mapping.keys (mapping_of (roth_translate a P)).
    roth_translate (\<lambda>v. - a v) (monom I (roth_taylor_coeff a I P)))"
  unfolding roth_taylor_coeff_def
  by (subst roth_translate_inverse[symmetric, of P a])
    (subst (1) roth_sum_monom[of "roth_translate a P"],
      simp add: roth_translate_def roth_mpoly_subst_sum)

lemma roth_taylor_identity_explicit:
  "P = (\<Sum>I\<in>Poly_Mapping.keys (mapping_of (roth_translate a P)).
    Const (roth_taylor_coeff a I P) *
      (\<Prod>v\<in>Poly_Mapping.keys I.
        (Var v - Const (a v)) ^ Poly_Mapping.lookup I v))"
  by (subst roth_taylor_identity[of P a])
    (simp add: roth_translate_def roth_mpoly_subst_monom
      roth_Const_uminus)

section \<open>Weighted index of a multivariate polynomial\<close>

definition roth_weight ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> real" where
  "roth_weight m r I =
    (\<Sum>v<m. real (Poly_Mapping.lookup I v) / real (r v))"

definition roth_index ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
    (nat \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> 'a mpoly \<Rightarrow> ereal" where
  "roth_index m r a P =
    Inf {ereal (roth_weight m r I) | I. roth_taylor_coeff a I P \<noteq> 0}"

lemma roth_weight_add:
  "roth_weight m r (I + J) = roth_weight m r I + roth_weight m r J"
  by (simp add: roth_weight_def lookup_add sum.distrib
    add_divide_distrib)

lemma roth_weight_nonneg:
  "0 \<le> roth_weight m r I"
  unfolding roth_weight_def
  by (intro sum_nonneg divide_nonneg_nonneg; simp)

lemma roth_inf_iff:
  "(theta::ereal) \<le> Inf S \<longleftrightarrow> (\<forall>x\<in>S. theta \<le> x)"
  by (metis Inf_greatest Inf_lower order_trans)

lemma roth_index_ge_iff:
  "(theta::ereal) \<le> roth_index m r a P \<longleftrightarrow>
    (\<forall>I. ereal (roth_weight m r I) < theta \<longrightarrow>
      roth_taylor_coeff a I P = 0)"
  by (auto simp: roth_index_def roth_inf_iff linorder_not_less)

lemma roth_index_translate:
  "roth_index m r a (roth_translate b P) =
    roth_index m r (\<lambda>v. a v + b v) P"
  by (simp add: roth_index_def roth_taylor_coeff_translate)

lemma roth_index_vanish_self:
  assumes "ereal (roth_weight m r I) < roth_index m r a P"
  shows "roth_taylor_coeff a I P = 0"
  using assms roth_index_ge_iff[of "roth_index m r a P" m r a P]
  by simp

lemma roth_index_add:
  "min (roth_index m r a P) (roth_index m r a Q) \<le>
    roth_index m r a (P + Q)"
  by (auto simp: roth_index_ge_iff roth_taylor_coeff_add
    roth_index_vanish_self)

lemma roth_index_le_coeff:
  assumes "roth_taylor_coeff a I P \<noteq> 0"
  shows "roth_index m r a P \<le> ereal (roth_weight m r I)"
  using assms by (auto simp: roth_index_def intro: Inf_lower)

lemma roth_index_mult_coeff:
  assumes c: "roth_taylor_coeff a I (P * Q) \<noteq> 0"
  shows "roth_index m r a P + roth_index m r a Q \<le>
    ereal (roth_weight m r I)"
proof -
  obtain J K where j: "roth_taylor_coeff a J P \<noteq> 0"
    and k: "roth_taylor_coeff a K Q \<noteq> 0"
    and i: "I = J + K"
    using roth_taylor_coeff_mult_support[OF c] by blast
  have h1: "roth_index m r a P \<le> ereal (roth_weight m r J)"
    using j by (rule roth_index_le_coeff)
  have h2: "roth_index m r a Q \<le> ereal (roth_weight m r K)"
    using k by (rule roth_index_le_coeff)
  have "roth_index m r a P + roth_index m r a Q \<le>
      ereal (roth_weight m r J) + ereal (roth_weight m r K)"
    by (rule add_mono[OF h1 h2])
  also have "\<dots> = ereal (roth_weight m r I)"
    by (simp add: i roth_weight_add)
  finally show ?thesis .
qed

lemma roth_index_mult:
  "roth_index m r a P + roth_index m r a Q \<le>
    roth_index m r a (P * Q)"
  by (auto simp: roth_index_ge_iff)
    (meson roth_index_mult_coeff linorder_not_less)

lemma roth_index_infty_iff:
  "roth_index m r a P = (\<infinity>::ereal) \<longleftrightarrow> P = 0"
  using roth_index_ge_iff[of "\<infinity>" m r a P]
  by (simp add: roth_taylor_coeff_all_zero)

lemma roth_index_zero [simp]:
  "roth_index m r a 0 = (\<infinity>::ereal)"
  by (simp add: roth_index_infty_iff)

lemma roth_index_nonneg:
  "(0::ereal) \<le> roth_index m r a P"
  by (auto simp: roth_index_ge_iff)
    (meson roth_weight_nonneg not_less)

lemma finite_roth_index_terms:
  "finite {ereal (roth_weight m r I) | I.
    roth_taylor_coeff a I P \<noteq> 0}"
  by (simp add: roth_taylor_coeff_key setcompr_eq_image)

lemma roth_index_attained:
  assumes p: "P \<noteq> 0"
  obtains I where
    "roth_taylor_coeff a I P \<noteq> 0"
    "roth_index m r a P = ereal (roth_weight m r I)"
proof -
  let ?S = "{ereal (roth_weight m r I) | I.
    roth_taylor_coeff a I P \<noteq> 0}"
  have fin: "finite ?S"
    by (rule finite_roth_index_terms)
  have ne: "?S \<noteq> {}"
    using p roth_taylor_coeff_all_zero by auto
  have "Min ?S \<in> ?S"
    by (rule Min_in[OF fin ne])
  then obtain I where c: "roth_taylor_coeff a I P \<noteq> 0"
    and e: "Min ?S = ereal (roth_weight m r I)"
    by auto
  have "roth_index m r a P = ereal (roth_weight m r I)"
    by (simp add: roth_index_def cInf_eq_Min[OF fin ne] e)
  then show ?thesis
    using that c by blast
qed

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
