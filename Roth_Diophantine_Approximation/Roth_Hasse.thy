theory Roth_Hasse
  imports
    Roth_MPoly_Box
    "Polynomials.MPoly_PM"
begin

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

end
