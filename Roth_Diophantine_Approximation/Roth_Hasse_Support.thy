theory Roth_Hasse_Support
  imports Roth_Hasse_Derivative
begin

section \<open>Exponent support of Hasse derivatives\<close>

definition roth_diagonal ::
  "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('a::idom mpoly) mpoly \<Rightarrow> bool" where
  "roth_diagonal K T \<longleftrightarrow>
    (\<forall>I J. coeff (coeff T J) I \<noteq> 0 \<longrightarrow> I + J = K)"

lemma roth_vars_one:
  "vars (1::'a::comm_ring_1 mpoly) = {}"
  using roth_Const_one[where 'a = 'a] roth_vars_Const
  by metis

lemma roth_vars_power_subset:
  fixes P :: "'a::comm_ring_1 mpoly"
  shows "vars (P ^ n) \<subseteq> vars P"
proof (induction n)
  case 0
  then show ?case by (simp add: roth_vars_one)
next
  case (Suc n)
  have "vars (P ^ Suc n) \<subseteq> vars P \<union> vars (P ^ n)"
    using vars_mult[of P "P ^ n"] by (simp add: power_Suc)
  then show ?case using Suc.IH by auto
qed

lemma roth_vars_prod_subset:
  fixes P :: "'i \<Rightarrow> 'a::comm_ring_1 mpoly"
  assumes "finite S"
  shows "vars (\<Prod>x\<in>S. P x) \<subseteq> (\<Union>x\<in>S. vars (P x))"
  using assms
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: roth_vars_one)
next
  case (insert x S)
  have "vars (\<Prod>y\<in>insert x S. P y) \<subseteq>
    vars (P x) \<union> vars (\<Prod>y\<in>S. P y)"
    using vars_mult[of "P x" "\<Prod>y\<in>S. P y"]
      insert.hyps by simp
  then show ?case using insert.IH by auto
qed

lemma roth_diagonal_smul:
  fixes T :: "('a::idom mpoly) mpoly"
  assumes d: "roth_diagonal K T"
  shows "roth_diagonal K (Const (Const c) * T)"
  unfolding roth_diagonal_def
proof (intro allI impI)
  fix I J
  assume nz: "coeff (coeff (Const (Const c) * T) J) I \<noteq> 0"
  have ce: "coeff (coeff (Const (Const c) * T) J) I =
    c * coeff (coeff T J) I"
    by (simp only: roth_coeff_Const_mult)
  have "coeff (coeff T J) I \<noteq> 0"
    using nz ce by auto
  then show "I + J = K"
    using d by (auto simp: roth_diagonal_def)
qed

lemma roth_diagonal_disjoint_mult:
  fixes T U :: "('a::idom mpoly) mpoly"
  assumes disj: "vars T \<inter> vars U = {}"
    and t: "roth_diagonal K T"
    and u: "roth_diagonal L U"
  shows "roth_diagonal (K + L) (T * U)"
  unfolding roth_diagonal_def
proof (intro allI impI)
  fix I J
  assume c: "coeff (coeff (T * U) J) I \<noteq> 0"
  have jnz: "coeff (T * U) J \<noteq> 0"
    using c by (auto simp: coeff_def zero_mpoly.rep_eq)
  have keyJ: "J \<in> Poly_Mapping.keys (mapping_of T * mapping_of U)"
    using jnz by (simp add: coeff_def in_keys_iff
      times_mpoly.rep_eq)
  obtain A B where a: "A \<in> Poly_Mapping.keys (mapping_of T)"
    and b: "B \<in> Poly_Mapping.keys (mapping_of U)"
    and j: "J = A + B"
    using keyJ by (metis in_keys_timesE)
  have ce: "coeff (T * U) J = coeff T A * coeff U B"
    using roth_disjoint_prod_coeff[OF disj a b] j by simp
  have inz: "coeff (coeff T A * coeff U B) I \<noteq> 0"
    using c ce by simp
  have keyI: "I \<in> Poly_Mapping.keys
    (mapping_of (coeff T A) * mapping_of (coeff U B))"
    using inz by (simp add: coeff_def in_keys_iff
      times_mpoly.rep_eq)
  obtain C D where ca: "C \<in> Poly_Mapping.keys (mapping_of (coeff T A))"
    and db: "D \<in> Poly_Mapping.keys (mapping_of (coeff U B))"
    and i: "I = C + D"
    using keyI by (metis in_keys_timesE)
  have ci: "coeff (coeff T A) C \<noteq> 0"
    using ca by (simp add: coeff_def in_keys_iff)
  have di: "coeff (coeff U B) D \<noteq> 0"
    using db by (simp add: coeff_def in_keys_iff)
  have ka: "C + A = K"
    using t ci by (auto simp: roth_diagonal_def)
  have lb: "D + B = L"
    using u di by (auto simp: roth_diagonal_def)
  have "I + J = (C + A) + (D + B)"
    using i j by (simp add: add_ac)
  then show "I + J = K + L"
    by (simp only: ka lb)
qed

lemma roth_diagonal_shift_Var_power:
  fixes v :: nat
  shows "roth_diagonal (Poly_Mapping.single v n)
    ((Var v + Const (Var v :: 'a::idom mpoly)) ^ n)"
  unfolding roth_diagonal_def
proof (intro allI impI)
  fix I J
  assume c: "coeff
    (coeff ((Var v + Const (Var v :: 'a mpoly)) ^ n) J) I \<noteq> 0"
  have e: "roth_hasse J ((Var v :: 'a mpoly) ^ n) =
    coeff ((Var v + Const (Var v)) ^ n) J"
    by (rule roth_hasse_Var_power)
  have "coeff (roth_hasse J ((Var v :: 'a mpoly) ^ n)) I \<noteq> 0"
    using c e by metis
  then show "I + J = Poly_Mapping.single v n"
    by (rule roth_hasse_Var_power_diagonal)
qed

lemma roth_diagonal_one:
  "roth_diagonal 0 (1::('a::idom mpoly) mpoly)"
  using roth_diagonal_shift_Var_power[of 0 0]
  by simp

lemma roth_vars_shift_power_subset:
  "vars ((Var v + Const (Var v :: 'a::comm_ring_1 mpoly)) ^ n)
    \<subseteq> {v}"
  using roth_vars_power_subset
      [of "Var v + Const (Var v :: 'a mpoly)" n]
    roth_vars_shift[of v "Var v :: 'a mpoly"]
  by auto

lemma roth_vars_shift_prod_subset:
  fixes K :: "nat \<Rightarrow>\<^sub>0 nat"
  assumes "finite S"
  shows "vars (\<Prod>v\<in>S.
    (Var v + Const (Var v :: 'a::comm_ring_1 mpoly)) ^
      Poly_Mapping.lookup K v) \<subseteq> S"
proof -
  have "vars (\<Prod>v\<in>S.
      (Var v + Const (Var v :: 'a mpoly)) ^
        Poly_Mapping.lookup K v) \<subseteq>
    (\<Union>v\<in>S. vars ((Var v + Const (Var v :: 'a mpoly)) ^
      Poly_Mapping.lookup K v))"
    by (rule roth_vars_prod_subset[OF assms])
  also have "\<dots> \<subseteq> S"
    using roth_vars_shift_power_subset by blast
  finally show ?thesis .
qed

lemma roth_keys_sum_single_subset:
  fixes j :: "nat \<Rightarrow> nat"
  assumes "finite S"
  shows "Poly_Mapping.keys
    (\<Sum>v\<in>S. Poly_Mapping.single v (j v)) \<subseteq> S"
  using assms
proof (induction S rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert v S)
  have h: "Poly_Mapping.keys
      (Poly_Mapping.single v (j v) +
        (\<Sum>w\<in>S. Poly_Mapping.single w (j w))) \<subseteq>
    Poly_Mapping.keys (Poly_Mapping.single v (j v)) \<union>
      Poly_Mapping.keys
        (\<Sum>w\<in>S. Poly_Mapping.single w (j w))"
    by (rule Poly_Mapping.keys_add)
  have sub: "Poly_Mapping.keys
      (Poly_Mapping.single v (j v) +
        (\<Sum>w\<in>S. Poly_Mapping.single w (j w))) \<subseteq>
    insert v S"
  proof
    fix x
    assume x: "x \<in> Poly_Mapping.keys
      (Poly_Mapping.single v (j v) +
        (\<Sum>w\<in>S. Poly_Mapping.single w (j w)))"
    have "x \<in> Poly_Mapping.keys (Poly_Mapping.single v (j v)) \<union>
      Poly_Mapping.keys
        (\<Sum>w\<in>S. Poly_Mapping.single w (j w))"
      using h x by blast
    then show "x \<in> insert v S"
      using insert.IH
      by (auto simp: Poly_Mapping.keys_single split: if_splits)
  qed
  show ?case using sub insert.hyps by simp
qed

lemma roth_coeff_prod_separate:
  fixes F :: "nat \<Rightarrow> ('a::idom mpoly) mpoly"
  assumes fin: "finite S"
    and fv: "\<And>v. v \<in> S \<Longrightarrow> vars (F v) \<subseteq> {v}"
  shows "coeff (\<Prod>v\<in>S. F v)
    (\<Sum>v\<in>S. Poly_Mapping.single v (j v)) =
    (\<Prod>v\<in>S.
      coeff (F v) (Poly_Mapping.single v (j v)))"
  using fin fv
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: coeff_def one_mpoly.rep_eq)
next
  case (insert v S)
  let ?G = "\<Prod>w\<in>S. F w"
  let ?J = "\<Sum>w\<in>S. Poly_Mapping.single w (j w)"
  have pa: "vars (F v) \<subseteq> {v}"
    using insert.prems by simp
  have qa: "vars ?G \<subseteq> S"
  proof -
    have "vars ?G \<subseteq> (\<Union>w\<in>S. vars (F w))"
      by (rule roth_vars_prod_subset[OF insert.hyps(1)])
    then show ?thesis using insert.prems by auto
  qed
  have isupp: "Poly_Mapping.keys
    (Poly_Mapping.single v (j v)) \<subseteq> {v}"
    by (simp add: Poly_Mapping.keys_single)
  have jsupp: "Poly_Mapping.keys ?J \<subseteq> S"
    by (rule roth_keys_sum_single_subset[OF insert.hyps(1)])
  have disj: "{v} \<inter> S = {}"
    using insert.hyps(2) by auto
  have ce: "coeff (F v * ?G)
      (Poly_Mapping.single v (j v) + ?J) =
    coeff (F v) (Poly_Mapping.single v (j v)) *
      coeff ?G ?J"
    by (rule roth_disjoint_prod_coeff_ambient
      [OF pa qa isupp jsupp disj])
  have ih: "coeff ?G ?J =
    (\<Prod>w\<in>S. coeff (F w)
      (Poly_Mapping.single w (j w)))"
    using insert.IH insert.prems by auto
  show ?case using ce ih insert.hyps by simp
qed

lemma roth_diagonal_shift_prod:
  fixes K :: "nat \<Rightarrow>\<^sub>0 nat"
  assumes "finite S"
  shows "roth_diagonal
    (\<Sum>v\<in>S. Poly_Mapping.single v (Poly_Mapping.lookup K v))
    (\<Prod>v\<in>S.
      (Var v + Const (Var v :: 'a::idom mpoly)) ^
        Poly_Mapping.lookup K v)"
  using assms
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: roth_diagonal_one)
next
  case (insert v S)
  let ?F = "(Var v + Const (Var v :: 'a mpoly)) ^
    Poly_Mapping.lookup K v"
  let ?G = "\<Prod>w\<in>S. (Var w + Const (Var w :: 'a mpoly)) ^
    Poly_Mapping.lookup K w"
  have fv: "roth_diagonal
    (Poly_Mapping.single v (Poly_Mapping.lookup K v)) ?F"
    by (rule roth_diagonal_shift_Var_power)
  have vs: "vars ?F \<subseteq> {v}"
    by (rule roth_vars_shift_power_subset)
  have ss: "vars ?G \<subseteq> S"
    by (rule roth_vars_shift_prod_subset[OF insert.hyps(1)])
  have disj: "vars ?F \<inter> vars ?G = {}"
    using vs ss insert.hyps(2) by auto
  have "roth_diagonal
    (Poly_Mapping.single v (Poly_Mapping.lookup K v) +
      (\<Sum>w\<in>S. Poly_Mapping.single w
        (Poly_Mapping.lookup K w))) (?F * ?G)"
    by (rule roth_diagonal_disjoint_mult[OF disj fv insert.IH])
  then show ?case using insert.hyps by simp
qed

lemma roth_sum_single_keys:
  fixes K :: "nat \<Rightarrow>\<^sub>0 nat"
  shows "(\<Sum>v\<in>Poly_Mapping.keys K.
    Poly_Mapping.single v (Poly_Mapping.lookup K v)) = K"
proof (rule Poly_Mapping.poly_mapping_eqI)
  fix v
  have lookup_term: "Poly_Mapping.lookup
    (Poly_Mapping.single w (Poly_Mapping.lookup K w)) v =
    (if w = v then Poly_Mapping.lookup K w else 0)" for w
    by (cases "w = v") (simp_all add: Poly_Mapping.lookup_single_not_eq)
  have "Poly_Mapping.lookup
      (\<Sum>w\<in>Poly_Mapping.keys K.
        Poly_Mapping.single w (Poly_Mapping.lookup K w)) v =
    (if v \<in> Poly_Mapping.keys K then Poly_Mapping.lookup K v else 0)"
    by (simp add: Poly_Mapping.lookup_sum lookup_term sum.If_cases)
  also have "\<dots> = Poly_Mapping.lookup K v"
    by (auto simp: not_in_keys_iff_lookup_eq_zero)
  finally show "Poly_Mapping.lookup
      (\<Sum>w\<in>Poly_Mapping.keys K.
        Poly_Mapping.single w (Poly_Mapping.lookup K w)) v =
      Poly_Mapping.lookup K v" .
qed

lemma roth_sum_single_on:
  fixes J :: "nat \<Rightarrow>\<^sub>0 nat"
  assumes "finite S" "Poly_Mapping.keys J \<subseteq> S"
  shows "(\<Sum>v\<in>S.
    Poly_Mapping.single v (Poly_Mapping.lookup J v)) = J"
proof (rule Poly_Mapping.poly_mapping_eqI)
  fix v
  have lookup_term: "Poly_Mapping.lookup
    (Poly_Mapping.single w (Poly_Mapping.lookup J w)) v =
    (if w = v then Poly_Mapping.lookup J w else 0)" for w
    by (cases "w = v") (simp_all add: Poly_Mapping.lookup_single_not_eq)
  have "Poly_Mapping.lookup
      (\<Sum>w\<in>S.
        Poly_Mapping.single w (Poly_Mapping.lookup J w)) v =
    (if v \<in> S then Poly_Mapping.lookup J v else 0)"
    using assms(1)
    by (simp add: Poly_Mapping.lookup_sum lookup_term sum.If_cases)
  also have "\<dots> = Poly_Mapping.lookup J v"
    using assms(2) by (auto simp: not_in_keys_iff_lookup_eq_zero)
  finally show "Poly_Mapping.lookup
      (\<Sum>w\<in>S.
        Poly_Mapping.single w (Poly_Mapping.lookup J w)) v =
      Poly_Mapping.lookup J v" .
qed

lemma roth_coeff_shift_prod:
  fixes K J :: "nat \<Rightarrow>\<^sub>0 nat"
  assumes fin: "finite S"
    and supp: "Poly_Mapping.keys J \<subseteq> S"
  shows "coeff
    (\<Prod>v\<in>S.
      (Var v + Const (Var v :: 'a::idom mpoly)) ^
        Poly_Mapping.lookup K v) J =
    (\<Prod>v\<in>S.
      coeff ((Var v + Const (Var v :: 'a mpoly)) ^
        Poly_Mapping.lookup K v)
        (Poly_Mapping.single v (Poly_Mapping.lookup J v)))"
proof -
  have vsub: "vars
      ((Var v + Const (Var v :: 'a mpoly)) ^
        Poly_Mapping.lookup K v) \<subseteq> {v}"
    if "v \<in> S" for v
    by (rule roth_vars_shift_power_subset)
  have eq: "(\<Sum>v\<in>S.
      Poly_Mapping.single v (Poly_Mapping.lookup J v)) = J"
    by (rule roth_sum_single_on[OF fin supp])
  show ?thesis
    using roth_coeff_prod_separate[OF fin vsub,
      of "\<lambda>v. Poly_Mapping.lookup J v"] eq by simp
qed

lemma roth_coeff_shift_power_single:
  "coeff ((Var v + Const (Var v :: 'a::idom mpoly)) ^ n)
    (Poly_Mapping.single v i) =
    (if i \<le> n then of_nat (n choose i) * Var v^(n-i) else 0)"
proof -
  have e: "roth_hasse (Poly_Mapping.single v i)
      ((Var v :: 'a mpoly)^n) =
    coeff ((Var v + Const (Var v)) ^ n)
      (Poly_Mapping.single v i)"
    by (rule roth_hasse_Var_power)
  have h: "roth_hasse (Poly_Mapping.single v i)
      ((Var v :: 'a mpoly)^n) =
    (if i \<le> n then of_nat (n choose i) * Var v^(n-i) else 0)"
    by (rule roth_hasse_Var_power_single)
  show ?thesis using e h by metis
qed

lemma roth_hasse_monom_product:
  fixes c :: "'a::idom"
  assumes supp: "Poly_Mapping.keys J \<subseteq> Poly_Mapping.keys K"
  shows "roth_hasse J (monom K c) =
    Const c * (\<Prod>v\<in>Poly_Mapping.keys K.
      (if Poly_Mapping.lookup J v \<le> Poly_Mapping.lookup K v
        then of_nat (Poly_Mapping.lookup K v choose
            Poly_Mapping.lookup J v) *
          Var v ^ (Poly_Mapping.lookup K v -
            Poly_Mapping.lookup J v)
        else 0))"
proof -
  have lift: "roth_lift (monom K c) = monom K (Const c)"
    by (simp add: roth_lift_def replace_coeff_monom roth_Const_zero)
  have expansion:
    "roth_translate Var (roth_lift (monom K c)) =
      Const (Const c) *
        (\<Prod>v\<in>Poly_Mapping.keys K.
          (Var v + Const (Var v)) ^ Poly_Mapping.lookup K v)"
    by (simp only: lift roth_translate_def roth_mpoly_subst_monom)
  have f: "coeff
      (\<Prod>v\<in>Poly_Mapping.keys K.
        (Var v + Const (Var v :: 'a mpoly)) ^
          Poly_Mapping.lookup K v) J =
    (\<Prod>v\<in>Poly_Mapping.keys K.
      coeff ((Var v + Const (Var v :: 'a mpoly)) ^
        Poly_Mapping.lookup K v)
        (Poly_Mapping.single v (Poly_Mapping.lookup J v)))"
    by (rule roth_coeff_shift_prod[OF _ supp]) simp
  have "roth_hasse J (monom K c) =
    coeff (roth_translate Var (roth_lift (monom K c))) J"
    by (simp only: roth_hasse_def roth_taylor_coeff_def)
  also have "\<dots> = Const c *
    coeff (\<Prod>v\<in>Poly_Mapping.keys K.
      (Var v + Const (Var v)) ^ Poly_Mapping.lookup K v) J"
    by (simp only: expansion roth_coeff_Const_mult)
  also have "\<dots> = Const c *
    (\<Prod>v\<in>Poly_Mapping.keys K.
      coeff ((Var v + Const (Var v)) ^
        Poly_Mapping.lookup K v)
        (Poly_Mapping.single v (Poly_Mapping.lookup J v)))"
    using f by simp
  also have "\<dots> = Const c * (\<Prod>v\<in>Poly_Mapping.keys K.
      (if Poly_Mapping.lookup J v \<le> Poly_Mapping.lookup K v
        then of_nat (Poly_Mapping.lookup K v choose
            Poly_Mapping.lookup J v) *
          Var v ^ (Poly_Mapping.lookup K v -
            Poly_Mapping.lookup J v)
        else 0))"
    by (simp add: roth_coeff_shift_power_single)
  finally show ?thesis .
qed

lemma roth_prod_monom:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
  assumes "finite S"
  shows "(\<Prod>v\<in>S. monom (Poly_Mapping.single v (n v)) (a v)) =
    monom (\<Sum>v\<in>S. Poly_Mapping.single v (n v))
      (\<Prod>v\<in>S. a v)"
  using assms
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: roth_Const_monom)
next
  case (insert v S)
  then show ?case by (simp add: mult_monom)
qed

lemma roth_prod_const_var:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
  assumes "finite S"
  shows "(\<Prod>v\<in>S. Const (a v) * Var v ^ n v) =
    monom (\<Sum>v\<in>S. Poly_Mapping.single v (n v))
      (\<Prod>v\<in>S. a v)"
proof -
  have e: "Const (a v) * (Var v :: 'a mpoly) ^ n v =
    monom (Poly_Mapping.single v (n v)) (a v)" for v
    by (simp only: roth_Var_power roth_Const_monom_left) simp
  show ?thesis
    by (simp only: e roth_prod_monom[OF assms])
qed

lemma roth_sum_single_sub:
  fixes K J :: "nat \<Rightarrow>\<^sub>0 nat"
  shows "(\<Sum>v\<in>Poly_Mapping.keys K.
    Poly_Mapping.single v
      (Poly_Mapping.lookup K v - Poly_Mapping.lookup J v)) = K - J"
proof (rule Poly_Mapping.poly_mapping_eqI)
  fix v
  have lookup_term: "Poly_Mapping.lookup
    (Poly_Mapping.single w
      (Poly_Mapping.lookup K w - Poly_Mapping.lookup J w)) v =
    (if w = v then Poly_Mapping.lookup K w -
      Poly_Mapping.lookup J w else 0)" for w
    by (cases "w = v") (simp_all add: Poly_Mapping.lookup_single_not_eq)
  have e: "Poly_Mapping.lookup
      (\<Sum>w\<in>Poly_Mapping.keys K.
        Poly_Mapping.single w
          (Poly_Mapping.lookup K w - Poly_Mapping.lookup J w)) v =
    (if v \<in> Poly_Mapping.keys K
      then Poly_Mapping.lookup K v - Poly_Mapping.lookup J v else 0)"
    by (simp add: Poly_Mapping.lookup_sum lookup_term sum.If_cases)
  show "Poly_Mapping.lookup
      (\<Sum>w\<in>Poly_Mapping.keys K.
        Poly_Mapping.single w
          (Poly_Mapping.lookup K w - Poly_Mapping.lookup J w)) v =
      Poly_Mapping.lookup (K-J) v"
    using e by (auto simp: lookup_minus not_in_keys_iff_lookup_eq_zero)
qed

definition roth_mchoose ::
  "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat" where
  "roth_mchoose K J =
    (\<Prod>v\<in>Poly_Mapping.keys K \<union> Poly_Mapping.keys J.
      Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v)"

lemma roth_mchoose_on:
  assumes "Poly_Mapping.keys J \<subseteq> Poly_Mapping.keys K"
  shows "roth_mchoose K J =
    (\<Prod>v\<in>Poly_Mapping.keys K.
      Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v)"
  using assms by (simp add: roth_mchoose_def sup.absorb1)

lemma roth_hasse_monom_exact_on:
  fixes c :: "'a::idom"
  assumes supp: "Poly_Mapping.keys J \<subseteq> Poly_Mapping.keys K"
    and le: "\<And>v. v \<in> Poly_Mapping.keys K \<Longrightarrow>
      Poly_Mapping.lookup J v \<le> Poly_Mapping.lookup K v"
  shows "roth_hasse J (monom K c) =
    monom (K-J) (c * of_nat (roth_mchoose K J))"
proof -
  let ?S = "Poly_Mapping.keys K"
  let ?b = "\<lambda>v. Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v"
  let ?n = "\<lambda>v. Poly_Mapping.lookup K v - Poly_Mapping.lookup J v"
  have e: "roth_hasse J (monom K c) =
    Const c * (\<Prod>v\<in>?S. of_nat (?b v) * Var v ^ ?n v)"
    using roth_hasse_monom_product[OF supp, of c] le
    by (simp cong: prod.cong)
  have f: "(\<Prod>v\<in>?S. of_nat (?b v) * (Var v :: 'a mpoly) ^ ?n v) =
    monom (\<Sum>v\<in>?S. Poly_Mapping.single v (?n v))
      (\<Prod>v\<in>?S. of_nat (?b v))"
    by (simp only: roth_of_nat_Const roth_prod_const_var[OF finite_keys])
  show ?thesis
    using e f
    by (simp only: roth_sum_single_sub roth_mchoose_on[OF supp]
      of_nat_prod roth_Const_monom_left)
qed

lemma roth_diagonal_monom:
  fixes c :: "'a::idom"
  shows "roth_diagonal K
    (roth_translate Var (roth_lift (monom K c)))"
proof -
  have lift: "roth_lift (monom K c) = monom K (Const c)"
    by (simp add: roth_lift_def replace_coeff_monom
      roth_Const_zero)
  have expansion:
    "roth_translate Var (roth_lift (monom K c)) =
      Const (Const c) *
        (\<Prod>v\<in>Poly_Mapping.keys K.
          (Var v + Const (Var v)) ^ Poly_Mapping.lookup K v)"
    by (simp only: lift roth_translate_def roth_mpoly_subst_monom)
  have d: "roth_diagonal
    (\<Sum>v\<in>Poly_Mapping.keys K.
      Poly_Mapping.single v (Poly_Mapping.lookup K v))
    (\<Prod>v\<in>Poly_Mapping.keys K.
      (Var v + Const (Var v :: 'a mpoly)) ^
        Poly_Mapping.lookup K v)"
    by (rule roth_diagonal_shift_prod) simp
  have "roth_diagonal K
    (Const (Const c) *
      (\<Prod>v\<in>Poly_Mapping.keys K.
        (Var v + Const (Var v :: 'a mpoly)) ^
          Poly_Mapping.lookup K v))"
    using d roth_sum_single_keys
    by (intro roth_diagonal_smul) simp
  then show ?thesis using expansion by simp
qed

lemma roth_hasse_monom_diagonal:
  fixes c :: "'a::idom"
  assumes "coeff (roth_hasse J (monom K c)) I \<noteq> 0"
  shows "I + J = K"
proof -
  have d: "roth_diagonal K
    (roth_translate Var (roth_lift (monom K c)))"
    by (rule roth_diagonal_monom)
  have e: "roth_hasse J (monom K c) =
    coeff (roth_translate Var (roth_lift (monom K c))) J"
    by (simp only: roth_hasse_def roth_taylor_coeff_def)
  show ?thesis
    using assms d e unfolding roth_diagonal_def by metis
qed

lemma roth_hasse_monom_zero:
  fixes c :: "'a::idom"
  assumes gt: "Poly_Mapping.lookup K v < Poly_Mapping.lookup J v"
  shows "roth_hasse J (monom K c) = 0"
proof -
  have z: "coeff (roth_hasse J (monom K c)) I = 0" for I
  proof (rule ccontr)
    assume "coeff (roth_hasse J (monom K c)) I \<noteq> 0"
    then have e: "I + J = K"
      by (rule roth_hasse_monom_diagonal)
    have "Poly_Mapping.lookup (I + J) v =
      Poly_Mapping.lookup K v"
      using e by simp
    then have "Poly_Mapping.lookup I v + Poly_Mapping.lookup J v =
      Poly_Mapping.lookup K v"
      by (simp only: lookup_add)
    with gt show False by arith
  qed
  show ?thesis using z
    by (simp add: coeff_eq[symmetric] fun_eq_iff
      coeff_def zero_mpoly.rep_eq)
qed

lemma roth_mchoose_zero:
  assumes gt: "Poly_Mapping.lookup K v < Poly_Mapping.lookup J v"
  shows "roth_mchoose K J = 0"
proof -
  have vin: "v \<in> Poly_Mapping.keys K \<union> Poly_Mapping.keys J"
    using gt by (auto simp: in_keys_iff)
  have "(\<Prod>w\<in>Poly_Mapping.keys K \<union> Poly_Mapping.keys J.
    Poly_Mapping.lookup K w choose Poly_Mapping.lookup J w) = 0"
    by (rule prod_zero) (use vin gt in auto)
  then show ?thesis by (simp only: roth_mchoose_def)
qed

lemma roth_hasse_monom_exact:
  fixes c :: "'a::idom"
  shows "roth_hasse J (monom K c) =
    monom (K-J) (c * of_nat (roth_mchoose K J))"
proof (cases "\<forall>v. Poly_Mapping.lookup J v \<le> Poly_Mapping.lookup K v")
  case True
  have supp: "Poly_Mapping.keys J \<subseteq> Poly_Mapping.keys K"
  proof
    fix v
    assume "v \<in> Poly_Mapping.keys J"
    then have "Poly_Mapping.lookup J v \<noteq> 0"
      by (simp add: in_keys_iff)
    with True have "Poly_Mapping.lookup K v \<noteq> 0"
      by (metis le_zero_eq)
    then show "v \<in> Poly_Mapping.keys K"
      by (simp add: in_keys_iff)
  qed
  show ?thesis
    by (rule roth_hasse_monom_exact_on[OF supp]) (use True in auto)
next
  case False
  then obtain v where gt:
    "Poly_Mapping.lookup K v < Poly_Mapping.lookup J v"
    by (meson not_le)
  have "roth_hasse J (monom K c) = 0"
    by (rule roth_hasse_monom_zero[OF gt])
  moreover have "roth_mchoose K J = 0"
    by (rule roth_mchoose_zero[OF gt])
  ultimately show ?thesis
    by (simp add: mapping_of_inject[symmetric]
      monom.rep_eq zero_mpoly.rep_eq)
qed

lemma roth_sub_add:
  fixes I J :: "nat \<Rightarrow>\<^sub>0 nat"
  shows "I + J - J = I"
  by (rule Poly_Mapping.poly_mapping_eqI)
    (simp add: lookup_minus lookup_add)

lemma roth_hasse_monom_coeff_exact:
  fixes c :: "'a::idom"
  shows "coeff (roth_hasse J (monom K c)) I =
    (if K = I + J then c * of_nat (roth_mchoose K J) else 0)"
proof (cases "K = I + J")
  case True
  then show ?thesis
    by (simp add: roth_hasse_monom_exact roth_sub_add coeff_monom)
next
  case False
  have "coeff (roth_hasse J (monom K c)) I = 0"
  proof (rule ccontr)
    assume "coeff (roth_hasse J (monom K c)) I \<noteq> 0"
    then have "I + J = K"
      by (rule roth_hasse_monom_diagonal)
    with False show False by simp
  qed
  with False show ?thesis by simp
qed

lemma roth_hasse_coeff_exact:
  fixes P :: "'a::idom mpoly"
  shows "coeff (roth_hasse J P) I =
    coeff P (I + J) * of_nat (roth_mchoose (I + J) J)"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of P)"
  have pe: "P = (\<Sum>K\<in>?S. monom K (coeff P K))"
    by (rule roth_sum_monom)
  have he: "roth_hasse J P =
    (\<Sum>K\<in>?S. roth_hasse J (monom K (coeff P K)))"
    using pe roth_hasse_sum[of ?S J
      "\<lambda>K. monom K (coeff P K)"] by simp
  have "coeff (roth_hasse J P) I =
    (\<Sum>K\<in>?S. coeff (roth_hasse J
      (monom K (coeff P K))) I)"
    by (simp only: he roth_coeff_sum[OF finite_keys])
  also have "\<dots> =
    (if I + J \<in> ?S
      then coeff P (I + J) * of_nat (roth_mchoose (I + J) J)
      else 0)"
    by (simp add: roth_hasse_monom_coeff_exact)
  also have "\<dots> =
    coeff P (I + J) * of_nat (roth_mchoose (I + J) J)"
    by (auto simp: coeff_def in_keys_iff)
  finally show ?thesis .
qed

lemma roth_mchoose_on_set:
  assumes fin: "finite S"
    and supp: "Poly_Mapping.keys K \<union> Poly_Mapping.keys J \<subseteq> S"
  shows "roth_mchoose K J =
    (\<Prod>v\<in>S.
      Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v)"
proof -
  have "(\<Prod>v\<in>Poly_Mapping.keys K \<union> Poly_Mapping.keys J.
      Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v) =
    (\<Prod>v\<in>S.
      Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v)"
    by (intro prod.mono_neutral_left[OF fin supp])
      (auto simp: not_in_keys_iff_lookup_eq_zero)
  then show ?thesis by (simp only: roth_mchoose_def)
qed

lemma roth_choose_comp_scalar:
  "(k+i+j choose j) * (k+i choose i) =
    (i+j choose i) * (k+i+j choose i+j)"
proof -
  have cm: "(k+i+j choose i+j) * (i+j choose j) =
    (k+i+j choose j) * (k+i choose i)"
    using choose_mult[of j "i+j" "k+i+j"] by simp
  have sym: "(i+j choose j) = (i+j choose i)"
    using binomial_symmetric[of j "i+j"] by simp
  show ?thesis using cm sym by (simp add: mult.commute)
qed

lemma roth_mchoose_comp:
  fixes K I J :: "nat \<Rightarrow>\<^sub>0 nat"
  shows "roth_mchoose (K+I+J) J * roth_mchoose (K+I) I =
    roth_mchoose (I+J) I * roth_mchoose (K+I+J) (I+J)"
proof -
  let ?S = "Poly_Mapping.keys K \<union> Poly_Mapping.keys I \<union>
    Poly_Mapping.keys J"
  have fin: "finite ?S" by simp
  have ki: "Poly_Mapping.keys (K+I) \<subseteq>
    Poly_Mapping.keys K \<union> Poly_Mapping.keys I"
    by (rule Poly_Mapping.keys_add)
  have ij: "Poly_Mapping.keys (I+J) \<subseteq>
    Poly_Mapping.keys I \<union> Poly_Mapping.keys J"
    by (rule Poly_Mapping.keys_add)
  have kij: "Poly_Mapping.keys (K+I+J) \<subseteq> ?S"
    using Poly_Mapping.keys_add[of "K+I" J] ki by auto
  have e1: "roth_mchoose (K+I+J) J =
    (\<Prod>v\<in>?S. Poly_Mapping.lookup (K+I+J) v choose
      Poly_Mapping.lookup J v)"
    by (rule roth_mchoose_on_set[OF fin]) (use kij in auto)
  have e2: "roth_mchoose (K+I) I =
    (\<Prod>v\<in>?S. Poly_Mapping.lookup (K+I) v choose
      Poly_Mapping.lookup I v)"
    by (rule roth_mchoose_on_set[OF fin]) (use ki in auto)
  have e3: "roth_mchoose (I+J) I =
    (\<Prod>v\<in>?S. Poly_Mapping.lookup (I+J) v choose
      Poly_Mapping.lookup I v)"
    by (rule roth_mchoose_on_set[OF fin]) (use ij in auto)
  have e4: "roth_mchoose (K+I+J) (I+J) =
    (\<Prod>v\<in>?S. Poly_Mapping.lookup (K+I+J) v choose
      Poly_Mapping.lookup (I+J) v)"
    by (rule roth_mchoose_on_set[OF fin]) (use kij ij in auto)
  have point: "(Poly_Mapping.lookup (K+I+J) v choose
      Poly_Mapping.lookup J v) *
      (Poly_Mapping.lookup (K+I) v choose
        Poly_Mapping.lookup I v) =
      (Poly_Mapping.lookup (I+J) v choose
        Poly_Mapping.lookup I v) *
      (Poly_Mapping.lookup (K+I+J) v choose
        Poly_Mapping.lookup (I+J) v)" for v
    by (simp add: lookup_add roth_choose_comp_scalar)
  show ?thesis
    unfolding e1 e2 e3 e4
    by (simp only: prod.distrib[symmetric])
      (rule prod.cong; simp add: point)
qed

lemma roth_hasse_comp:
  fixes P :: "'a::idom mpoly"
  shows "roth_hasse I (roth_hasse J P) =
    Const (of_nat (roth_mchoose (I+J) I)) *
      roth_hasse (I+J) P"
proof -
  have ce: "coeff (roth_hasse I (roth_hasse J P)) K =
    coeff (Const (of_nat (roth_mchoose (I+J) I)) *
      roth_hasse (I+J) P) K" for K
  proof -
    have lhs: "coeff (roth_hasse I (roth_hasse J P)) K =
      coeff P (K+I+J) *
        of_nat (roth_mchoose (K+I+J) J) *
        of_nat (roth_mchoose (K+I) I)"
      by (simp add: roth_hasse_coeff_exact add.assoc)
    have rhs: "coeff (Const (of_nat (roth_mchoose (I+J) I)) *
        roth_hasse (I+J) P) K =
      of_nat (roth_mchoose (I+J) I) *
        (coeff P (K+I+J) *
          of_nat (roth_mchoose (K+I+J) (I+J)))"
      by (simp add: roth_coeff_Const_mult roth_hasse_coeff_exact
        add.assoc)
    have binom: "of_nat (roth_mchoose (K+I+J) J) *
        of_nat (roth_mchoose (K+I) I) =
      (of_nat (roth_mchoose (I+J) I) :: 'a) *
        of_nat (roth_mchoose (K+I+J) (I+J))"
      using roth_mchoose_comp[of K I J]
      by (simp only: of_nat_mult[symmetric])
    show ?thesis using lhs rhs binom by (simp add: algebra_simps)
  qed
  show ?thesis using ce
    by (simp add: coeff_eq[symmetric] fun_eq_iff)
qed

lemma roth_mchoose_box_bound:
  assumes box: "K \<in> roth_exponent_box m r"
  shows "roth_mchoose K J \<le> 2 ^ (\<Sum>v<m. r v)"
proof (cases "roth_mchoose K J = 0")
  case True
  then show ?thesis by simp
next
  case False
  have jle: "Poly_Mapping.lookup J v \<le> Poly_Mapping.lookup K v"
    for v
    using False roth_mchoose_zero[of K v J] by (meson not_le)
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
    by (rule roth_exponent_boxD(1)[OF box])
  have e: "roth_mchoose K J =
    (\<Prod>v<m.
      Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v)"
    by (rule roth_mchoose_on_set) (use jsupp ksupp in auto)
  have point: "Poly_Mapping.lookup K v choose
      Poly_Mapping.lookup J v \<le> 2 ^ r v" if "v < m" for v
  proof -
    have kbound: "Poly_Mapping.lookup K v \<le> r v"
      by (rule roth_exponent_boxD(2)[OF box that])
    have a: "Poly_Mapping.lookup K v choose
      Poly_Mapping.lookup J v \<le>
      2 ^ Poly_Mapping.lookup K v"
      by (rule binomial_le_pow2)
    have b: "(2::nat) ^ Poly_Mapping.lookup K v \<le> 2 ^ r v"
      using kbound by (simp add: power_increasing)
    show ?thesis using a b by arith
  qed
  have "(\<Prod>v<m.
      Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v)
    \<le> (\<Prod>v<m. 2 ^ r v)"
    by (intro prod_mono) (use point in auto)
  also have "\<dots> = 2 ^ (\<Sum>v<m. r v)"
    by (simp only: power_sum)
  finally show ?thesis using e by simp
qed

lemma roth_hasse_coeff_bound:
  fixes P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "abs (coeff (roth_hasse J P) I) \<le>
    int (2 ^ (\<Sum>v<m. r v)) * abs (coeff P (I+J))"
proof (cases "coeff P (I+J) = 0")
  case True
  then show ?thesis by (simp add: roth_hasse_coeff_exact)
next
  case False
  have mem: "I+J \<in> roth_exponent_box m r"
    using box False
    by (auto simp: roth_poly_in_box_def coeff_def in_keys_iff)
  have b: "roth_mchoose (I+J) J \<le> 2 ^ (\<Sum>v<m. r v)"
    by (rule roth_mchoose_box_bound[OF mem])
  have mult: "abs (coeff P (I+J)) *
      int (roth_mchoose (I+J) J) \<le>
    abs (coeff P (I+J)) * int (2 ^ (\<Sum>v<m. r v))"
    using b by (intro mult_left_mono) auto
  show ?thesis using mult
    by (simp add: roth_hasse_coeff_exact abs_mult mult.commute)
qed

lemma roth_hasse_coeff_support:
  fixes P :: "'a::idom mpoly"
  assumes nz: "coeff (roth_hasse J P) I \<noteq> 0"
  shows "coeff P (I + J) \<noteq> 0"
  using nz by (auto simp: roth_hasse_coeff_exact)

lemma roth_hasse_taylor_support:
  fixes P :: "'a::idom mpoly"
  assumes nz: "roth_taylor_coeff a J (roth_hasse I P) \<noteq> 0"
  shows "roth_taylor_coeff a (I + J) P \<noteq> 0"
proof -
  have e: "roth_translate a (roth_hasse I P) =
    roth_hasse I (roth_translate a P)"
    by (simp only: roth_hasse_translate)
  have c: "coeff (roth_hasse I (roth_translate a P)) J \<noteq> 0"
    using nz e by (simp add: roth_taylor_coeff_def)
  have "coeff (roth_translate a P) (J + I) \<noteq> 0"
    by (rule roth_hasse_coeff_support[OF c])
  then show ?thesis
    by (simp add: roth_taylor_coeff_def add.commute)
qed

lemma roth_index_hasse_add:
  fixes P :: "'a::idom mpoly"
  shows "roth_index m r a P \<le>
    ereal (roth_weight m r I) +
      roth_index m r a (roth_hasse I P)"
proof (cases "roth_hasse I P = 0")
  case True
  then show ?thesis by simp
next
  case False
  obtain J where c: "roth_taylor_coeff a J (roth_hasse I P) \<noteq> 0"
    and j: "roth_index m r a (roth_hasse I P) =
      ereal (roth_weight m r J)"
    using roth_index_attained[OF False] by blast
  have cp: "roth_taylor_coeff a (I + J) P \<noteq> 0"
    by (rule roth_hasse_taylor_support[OF c])
  have le: "roth_index m r a P \<le>
    ereal (roth_weight m r (I + J))"
    by (rule roth_index_le_coeff[OF cp])
  show ?thesis using le j
    by (simp add: roth_weight_add)
qed

lemma roth_index_hasse:
  fixes P :: "'a::idom mpoly"
  shows "roth_index m r a P -
    ereal (roth_weight m r I) \<le>
      roth_index m r a (roth_hasse I P)"
proof -
  have le: "roth_index m r a P \<le>
    ereal (roth_weight m r I) +
      roth_index m r a (roth_hasse I P)"
    by (rule roth_index_hasse_add)
  have eq: "roth_index m r a P -
      ereal (roth_weight m r I) \<le>
        roth_index m r a (roth_hasse I P)
    \<longleftrightarrow> roth_index m r a P \<le>
      roth_index m r a (roth_hasse I P) +
        ereal (roth_weight m r I)"
    by (rule ereal_minus_le) simp
  show ?thesis using le by (simp add: eq add.commute)
qed

lemma roth_hasse_in_box:
  fixes P :: "'a::idom mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "roth_poly_in_box m
    (\<lambda>v. r v - Poly_Mapping.lookup I v) (roth_hasse I P)"
proof (unfold roth_poly_in_box_def, intro subsetI)
  fix K
  assume key: "K \<in> Poly_Mapping.keys (mapping_of (roth_hasse I P))"
  have c: "coeff (roth_hasse I P) K \<noteq> 0"
    using key by (simp add: coeff_def in_keys_iff)
  have cp: "coeff P (K + I) \<noteq> 0"
    by (rule roth_hasse_coeff_support[OF c])
  have orig: "K + I \<in> roth_exponent_box m r"
    using box cp by (auto simp: roth_poly_in_box_def
      coeff_def in_keys_iff)
  have orig_vars: "Poly_Mapping.keys (K + I) \<subseteq> {..<m}"
    by (rule roth_exponent_boxD(1)[OF orig])
  show "K \<in> roth_exponent_box m
    (\<lambda>v. r v - Poly_Mapping.lookup I v)"
  proof (rule roth_exponent_boxI)
    show "Poly_Mapping.keys K \<subseteq> {..<m}"
    proof
      fix v
      assume vk: "v \<in> Poly_Mapping.keys K"
      show "v \<in> {..<m}"
      proof (rule ccontr)
        assume vo: "v \<notin> {..<m}"
        have "Poly_Mapping.lookup (K + I) v = 0"
          by (rule roth_lookup_zero_outside[OF orig_vars vo])
        then have "Poly_Mapping.lookup K v = 0"
          by (simp add: lookup_add)
        then show False using vk
          by (simp add: in_keys_iff)
      qed
    qed
    fix v
    assume vm: "v < m"
    have "Poly_Mapping.lookup (K + I) v \<le> r v"
      by (rule roth_exponent_boxD(2)[OF orig vm])
    then show "Poly_Mapping.lookup K v \<le>
      r v - Poly_Mapping.lookup I v"
      by (simp add: lookup_add)
  qed
qed

lemma roth_hasse_degree_bound:
  fixes P :: "'a::idom mpoly"
  assumes "roth_poly_in_box m r P" "v < m"
  shows "MPoly_Type.degree (roth_hasse I P) v \<le>
    r v - Poly_Mapping.lookup I v"
  using roth_degree_le_of_box[OF roth_hasse_in_box[OF assms(1)]
      assms(2)] .

end
