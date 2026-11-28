theory MPoly_Hasse_Support
  imports MPoly_Hasse_Derivative
begin

section \<open>Exponent support of Hasse derivatives\<close>

definition pjet_diagonal ::
  "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('a::idom mpoly) mpoly \<Rightarrow> bool" where
  "pjet_diagonal K T \<equiv>
    (\<forall>I J. coeff (coeff T J) I \<noteq> 0 \<longrightarrow> I + J = K)"

lemma pjet_vars_one:
  "vars (1::'a::comm_ring_1 mpoly) = {}"
  using pjet_Const_one[where 'a = 'a] pjet_vars_Const
  by metis

lemma pjet_vars_power_subset:
  fixes P :: "'a::comm_ring_1 mpoly"
  shows "vars (P ^ n) \<subseteq> vars P"
proof (induction n)
  case 0
  then show ?case by (simp add: pjet_vars_one)
next
  case (Suc n)
  have "vars (P ^ Suc n) \<subseteq> vars P \<union> vars (P ^ n)"
    using vars_mult[of P "P ^ n"] by simp
  then show ?case using Suc.IH by auto
qed

lemma pjet_vars_prod_subset:
  fixes P :: "'i \<Rightarrow> 'a::comm_ring_1 mpoly"
  assumes "finite S"
  shows "vars (\<Prod>x\<in>S. P x) \<subseteq> (\<Union>x\<in>S. vars (P x))"
  using assms
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: pjet_vars_one)
next
  case (insert x S)
  have "vars (\<Prod>y\<in>insert x S. P y) \<subseteq>
    vars (P x) \<union> vars (\<Prod>y\<in>S. P y)"
    using vars_mult[of "P x" "\<Prod>y\<in>S. P y"]
      insert.hyps by simp
  then show ?case using insert.IH by auto
qed

lemma pjet_diagonal_smul:
  fixes T :: "('a::idom mpoly) mpoly"
  assumes d: "pjet_diagonal K T"
  shows "pjet_diagonal K (Const (Const c) * T)"
  unfolding pjet_diagonal_def
proof (intro allI impI)
  fix I J
  assume nz: "coeff (coeff (Const (Const c) * T) J) I \<noteq> 0"
  have ce: "coeff (coeff (Const (Const c) * T) J) I =
    c * coeff (coeff T J) I"
    by (simp only: pjet_coeff_Const_mult)
  have "coeff (coeff T J) I \<noteq> 0"
    using nz ce by auto
  then show "I + J = K"
    using d by (auto simp: pjet_diagonal_def)
qed

lemma pjet_diagonal_disjoint_mult:
  fixes T U :: "('a::idom mpoly) mpoly"
  assumes disj: "vars T \<inter> vars U = {}"
    and t: "pjet_diagonal K T"
    and u: "pjet_diagonal L U"
  shows "pjet_diagonal (K + L) (T * U)"
  unfolding pjet_diagonal_def
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
    using pjet_disjoint_prod_coeff[OF disj a b] j by simp
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
    using t ci by (auto simp: pjet_diagonal_def)
  have lb: "D + B = L"
    using u di by (auto simp: pjet_diagonal_def)
  have "I + J = (C + A) + (D + B)"
    using i j by (simp add: add_ac)
  then show "I + J = K + L"
    by (simp only: ka lb)
qed

lemma pjet_diagonal_shift_Var_power:
  fixes v :: nat
  shows "pjet_diagonal (Poly_Mapping.single v n)
    ((Var v + Const (Var v :: 'a::idom mpoly)) ^ n)"
  unfolding pjet_diagonal_def
proof (intro allI impI)
  fix I J
  assume c: "coeff
    (coeff ((Var v + Const (Var v :: 'a mpoly)) ^ n) J) I \<noteq> 0"
  have e: "pjet_hasse J ((Var v :: 'a mpoly) ^ n) =
    coeff ((Var v + Const (Var v)) ^ n) J"
    by (rule pjet_hasse_Var_power)
  have "coeff (pjet_hasse J ((Var v :: 'a mpoly) ^ n)) I \<noteq> 0"
    using c e by metis
  then show "I + J = Poly_Mapping.single v n"
    by (rule pjet_hasse_Var_power_diagonal)
qed

lemma pjet_diagonal_one:
  "pjet_diagonal 0 (1::('a::idom mpoly) mpoly)"
  using pjet_diagonal_shift_Var_power[of 0 0]
  by simp

lemma pjet_vars_shift_power_subset:
  "vars ((Var v + Const (Var v :: 'a::comm_ring_1 mpoly)) ^ n)
    \<subseteq> {v}"
  using pjet_vars_power_subset
      [of "Var v + Const (Var v :: 'a mpoly)" n]
    pjet_vars_shift[of v "Var v :: 'a mpoly"]
  by auto

lemma pjet_vars_shift_prod_subset:
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
    by (rule pjet_vars_prod_subset[OF assms])
  also have "\<dots> \<subseteq> S"
    using pjet_vars_shift_power_subset by blast
  finally show ?thesis .
qed

lemma pjet_keys_sum_single_subset:
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
      using insert.IH by (auto split: if_splits)
  qed
  show ?case using sub insert.hyps by simp
qed

lemma pjet_coeff_prod_separate:
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
      by (rule pjet_vars_prod_subset[OF insert.hyps(1)])
    then show ?thesis using insert.prems by auto
  qed
  have isupp: "Poly_Mapping.keys
    (Poly_Mapping.single v (j v)) \<subseteq> {v}"
    by simp
  have jsupp: "Poly_Mapping.keys ?J \<subseteq> S"
    by (rule pjet_keys_sum_single_subset[OF insert.hyps(1)])
  have disj: "{v} \<inter> S = {}"
    using insert.hyps(2) by auto
  have ce: "coeff (F v * ?G)
      (Poly_Mapping.single v (j v) + ?J) =
    coeff (F v) (Poly_Mapping.single v (j v)) *
      coeff ?G ?J"
    by (rule pjet_disjoint_prod_coeff_ambient
      [OF pa qa isupp jsupp disj])
  have ih: "coeff ?G ?J =
    (\<Prod>w\<in>S. coeff (F w)
      (Poly_Mapping.single w (j w)))"
    using insert.IH insert.prems by auto
  show ?case using ce ih insert.hyps by simp
qed

lemma pjet_diagonal_shift_prod:
  fixes K :: "nat \<Rightarrow>\<^sub>0 nat"
  assumes "finite S"
  shows "pjet_diagonal
    (\<Sum>v\<in>S. Poly_Mapping.single v (Poly_Mapping.lookup K v))
    (\<Prod>v\<in>S.
      (Var v + Const (Var v :: 'a::idom mpoly)) ^
        Poly_Mapping.lookup K v)"
  using assms
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: pjet_diagonal_one)
next
  case (insert v S)
  let ?F = "(Var v + Const (Var v :: 'a mpoly)) ^
    Poly_Mapping.lookup K v"
  let ?G = "\<Prod>w\<in>S. (Var w + Const (Var w :: 'a mpoly)) ^
    Poly_Mapping.lookup K w"
  have fv: "pjet_diagonal
    (Poly_Mapping.single v (Poly_Mapping.lookup K v)) ?F"
    by (rule pjet_diagonal_shift_Var_power)
  have vs: "vars ?F \<subseteq> {v}"
    by (rule pjet_vars_shift_power_subset)
  have ss: "vars ?G \<subseteq> S"
    by (rule pjet_vars_shift_prod_subset[OF insert.hyps(1)])
  have disj: "vars ?F \<inter> vars ?G = {}"
    using vs ss insert.hyps(2) by auto
  have "pjet_diagonal
    (Poly_Mapping.single v (Poly_Mapping.lookup K v) +
      (\<Sum>w\<in>S. Poly_Mapping.single w
        (Poly_Mapping.lookup K w))) (?F * ?G)"
    by (rule pjet_diagonal_disjoint_mult[OF disj fv insert.IH])
  then show ?case using insert.hyps by simp
qed

lemma pjet_sum_single_keys:
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

lemma pjet_sum_single_on:
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
    using \<open>finite S\<close>
    by (simp add: Poly_Mapping.lookup_sum lookup_term sum.If_cases)
  also have "\<dots> = Poly_Mapping.lookup J v"
    using \<open>Poly_Mapping.keys J \<subseteq> S\<close> by (auto simp: not_in_keys_iff_lookup_eq_zero)
  finally show "Poly_Mapping.lookup
      (\<Sum>w\<in>S.
        Poly_Mapping.single w (Poly_Mapping.lookup J w)) v =
      Poly_Mapping.lookup J v" .
qed

lemma pjet_coeff_shift_prod:
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
    by (rule pjet_vars_shift_power_subset)
  have eq: "(\<Sum>v\<in>S.
      Poly_Mapping.single v (Poly_Mapping.lookup J v)) = J"
    by (rule pjet_sum_single_on[OF fin supp])
  show ?thesis
    using pjet_coeff_prod_separate[OF fin vsub,
      of "\<lambda>v. Poly_Mapping.lookup J v"] eq by simp
qed

lemma pjet_coeff_shift_power_single:
  "coeff ((Var v + Const (Var v :: 'a::idom mpoly)) ^ n)
    (Poly_Mapping.single v i) =
    (if i \<le> n then of_nat (n choose i) * Var v^(n-i) else 0)"
proof -
  have e: "pjet_hasse (Poly_Mapping.single v i)
      ((Var v :: 'a mpoly)^n) =
    coeff ((Var v + Const (Var v)) ^ n)
      (Poly_Mapping.single v i)"
    by (rule pjet_hasse_Var_power)
  have h: "pjet_hasse (Poly_Mapping.single v i)
      ((Var v :: 'a mpoly)^n) =
    (if i \<le> n then of_nat (n choose i) * Var v^(n-i) else 0)"
    by (rule pjet_hasse_Var_power_single)
  show ?thesis using e h by metis
qed

lemma pjet_hasse_monom_product:
  fixes c :: "'a::idom"
  assumes supp: "Poly_Mapping.keys J \<subseteq> Poly_Mapping.keys K"
  shows "pjet_hasse J (monom K c) =
    Const c * (\<Prod>v\<in>Poly_Mapping.keys K.
      (if Poly_Mapping.lookup J v \<le> Poly_Mapping.lookup K v
        then of_nat (Poly_Mapping.lookup K v choose
            Poly_Mapping.lookup J v) *
          Var v ^ (Poly_Mapping.lookup K v -
            Poly_Mapping.lookup J v)
        else 0))"
proof -
  have lift: "pjet_lift (monom K c) = monom K (Const c)"
    by (simp add: pjet_lift_def replace_coeff_monom)
  have expansion:
    "pjet_translate Var (pjet_lift (monom K c)) =
      Const (Const c) *
        (\<Prod>v\<in>Poly_Mapping.keys K.
          (Var v + Const (Var v)) ^ Poly_Mapping.lookup K v)"
    by (simp only: lift pjet_translate_def pjet_mpoly_subst_monom)
  have f: "coeff
      (\<Prod>v\<in>Poly_Mapping.keys K.
        (Var v + Const (Var v :: 'a mpoly)) ^
          Poly_Mapping.lookup K v) J =
    (\<Prod>v\<in>Poly_Mapping.keys K.
      coeff ((Var v + Const (Var v :: 'a mpoly)) ^
        Poly_Mapping.lookup K v)
        (Poly_Mapping.single v (Poly_Mapping.lookup J v)))"
    by (rule pjet_coeff_shift_prod[OF _ supp]) simp
  have "pjet_hasse J (monom K c) =
    coeff (pjet_translate Var (pjet_lift (monom K c))) J"
    by (simp only: pjet_hasse_def pjet_taylor_coeff_def)
  also have "\<dots> = Const c *
    coeff (\<Prod>v\<in>Poly_Mapping.keys K.
      (Var v + Const (Var v)) ^ Poly_Mapping.lookup K v) J"
    by (simp only: expansion pjet_coeff_Const_mult)
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
    by (simp add: pjet_coeff_shift_power_single)
  finally show ?thesis .
qed

lemma pjet_prod_monom:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
  assumes "finite S"
  shows "(\<Prod>v\<in>S. monom (Poly_Mapping.single v (n v)) (a v)) =
    monom (\<Sum>v\<in>S. Poly_Mapping.single v (n v))
      (\<Prod>v\<in>S. a v)"
  using assms
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: pjet_Const_monom)
next
  case (insert v S)
  then show ?case by (simp add: mult_monom)
qed

lemma pjet_prod_const_var:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
  assumes "finite S"
  shows "(\<Prod>v\<in>S. Const (a v) * Var v ^ n v) =
    monom (\<Sum>v\<in>S. Poly_Mapping.single v (n v)) (\<Prod>v\<in>S. a v)"
using assms by (metis (no_types, lifting) ext pjet_Var_power pjet_monom_smul pjet_prod_monom)

lemma pjet_sum_single_sub:
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
    by (simp add: Poly_Mapping.lookup_single_not_eq)
  show "Poly_Mapping.lookup
      (\<Sum>w\<in>Poly_Mapping.keys K.
        Poly_Mapping.single w
          (Poly_Mapping.lookup K w - Poly_Mapping.lookup J w)) v =
      Poly_Mapping.lookup (K-J) v"
    by (auto simp: Poly_Mapping.lookup_sum lookup_term sum.If_cases lookup_minus not_in_keys_iff_lookup_eq_zero)
qed

definition pjet_mchoose ::
  "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat" where
  "pjet_mchoose K J \<equiv>
    (\<Prod>v\<in>Poly_Mapping.keys K \<union> Poly_Mapping.keys J.
      Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v)"

lemma pjet_mchoose_on:
  assumes "Poly_Mapping.keys J \<subseteq> Poly_Mapping.keys K"
  shows "pjet_mchoose K J =
    (\<Prod>v\<in>Poly_Mapping.keys K.
      Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v)"
  using assms by (simp add: pjet_mchoose_def sup.absorb1)

lemma pjet_hasse_monom_exact_on:
  fixes c :: "'a::idom"
  assumes supp: "Poly_Mapping.keys J \<subseteq> Poly_Mapping.keys K"
    and le: "\<And>v. v \<in> Poly_Mapping.keys K \<Longrightarrow>
      Poly_Mapping.lookup J v \<le> Poly_Mapping.lookup K v"
  shows "pjet_hasse J (monom K c) =
    monom (K-J) (c * of_nat (pjet_mchoose K J))"
proof -
  let ?S = "Poly_Mapping.keys K"
  let ?b = "\<lambda>v. Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v"
  let ?n = "\<lambda>v. Poly_Mapping.lookup K v - Poly_Mapping.lookup J v"
  have e: "pjet_hasse J (monom K c) =
    Const c * (\<Prod>v\<in>?S. of_nat (?b v) * Var v ^ ?n v)"
    using pjet_hasse_monom_product[OF supp, of c] le
    by (simp cong: prod.cong)
  have f: "(\<Prod>v\<in>?S. of_nat (?b v) * (Var v :: 'a mpoly) ^ ?n v) =
    monom (\<Sum>v\<in>?S. Poly_Mapping.single v (?n v))
      (\<Prod>v\<in>?S. of_nat (?b v))"
    by (simp only: pjet_of_nat_Const pjet_prod_const_var[OF finite_keys])
  show ?thesis
    using e f
    by (simp only: pjet_sum_single_sub pjet_mchoose_on[OF supp]
      of_nat_prod pjet_Const_monom_left)
qed

lemma pjet_diagonal_monom:
  fixes c :: "'a::idom"
  shows "pjet_diagonal K (pjet_translate Var (pjet_lift (monom K c)))"
proof -
  have "pjet_diagonal K
    (Const (Const c) *
      (\<Prod>v\<in>Poly_Mapping.keys K.
        (Var v + Const (Var v :: 'a mpoly)) ^
          Poly_Mapping.lookup K v))"
    by (metis (mono_tags, lifting) finite_keys pjet_diagonal_shift_prod pjet_diagonal_smul pjet_sum_single_keys)
  then show ?thesis unfolding pjet_translate_def
    by (simp add: pjet_lift_def replace_coeff_monom pjet_Const_zero pjet_mpoly_subst_monom)
qed

lemma pjet_hasse_monom_diagonal:
  fixes c :: "'a::idom"
  assumes "coeff (pjet_hasse J (monom K c)) I \<noteq> 0"
  shows "I + J = K"
proof -
  have e: "pjet_hasse J (monom K c) =
    coeff (pjet_translate Var (pjet_lift (monom K c))) J"
    by (simp only: pjet_hasse_def pjet_taylor_coeff_def)
  show ?thesis
    using assms pjet_diagonal_monom e unfolding pjet_diagonal_def by metis
qed

lemma pjet_hasse_monom_zero:
  fixes c :: "'a::idom"
  assumes gt: "Poly_Mapping.lookup K v < Poly_Mapping.lookup J v"
  shows "pjet_hasse J (monom K c) = 0"
proof -
  have "coeff (pjet_hasse J (monom K c)) I = 0" for I
    using gt by (metis add.commute lookup_add not_add_less1 pjet_hasse_monom_diagonal)
  then show ?thesis
    by (simp add: coeff_eq[symmetric] fun_eq_iff coeff_def zero_mpoly.rep_eq)
qed

lemma pjet_mchoose_zero:
  assumes gt: "Poly_Mapping.lookup K v < Poly_Mapping.lookup J v"
  shows "pjet_mchoose K J = 0"
proof -
  have vin: "v \<in> Poly_Mapping.keys K \<union> Poly_Mapping.keys J"
    using gt by (auto simp: in_keys_iff)
  have "(\<Prod>w\<in>Poly_Mapping.keys K \<union> Poly_Mapping.keys J.
    Poly_Mapping.lookup K w choose Poly_Mapping.lookup J w) = 0"
    by (rule prod_zero) (use vin gt in auto)
  then show ?thesis by (simp only: pjet_mchoose_def)
qed

lemma pjet_hasse_monom_exact:
  fixes c :: "'a::idom"
  shows "pjet_hasse J (monom K c) =
    monom (K-J) (c * of_nat (pjet_mchoose K J))"
proof (cases "\<forall>v. Poly_Mapping.lookup J v \<le> Poly_Mapping.lookup K v")
  case True
  have supp: "Poly_Mapping.keys J \<subseteq> Poly_Mapping.keys K"
    using True by (metis in_keys_iff le_0_eq subsetI)
  show ?thesis
    by (rule pjet_hasse_monom_exact_on[OF supp]) (use True in auto)
next
  case False
    then have "pjet_hasse J (monom K c) = 0"
      using linorder_not_less pjet_hasse_monom_zero by fastforce
  moreover have "pjet_mchoose K J = 0"
  using False by (meson linorder_not_le pjet_mchoose_zero)
  ultimately show ?thesis
    by (simp add: mapping_of_inject[symmetric]
      monom.rep_eq zero_mpoly.rep_eq)
qed

lemma pjet_hasse_monom_coeff_exact:
  fixes c :: "'a::idom"
  shows "coeff (pjet_hasse J (monom K c)) I =
    (if K = I + J then c * of_nat (pjet_mchoose K J) else 0)"
proof (cases "K = I + J")
  case True
  then show ?thesis
    by (simp add: pjet_hasse_monom_exact add_diff_cancel_right' coeff_monom)
next
  case False
  with pjet_hasse_monom_diagonal show ?thesis by force
qed

lemma pjet_hasse_coeff_exact:
  fixes P :: "'a::idom mpoly"
  shows "coeff (pjet_hasse J P) I =
    coeff P (I + J) * of_nat (pjet_mchoose (I + J) J)"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of P)"
  have "coeff (pjet_hasse J P) I =
    (\<Sum>K\<in>?S. coeff (pjet_hasse J
      (monom K (coeff P K))) I)"
    using pjet_sum_monom pjet_hasse_sum[of ?S J "\<lambda>K. monom K (coeff P K)"] pjet_coeff_sum
    by (metis (no_types, lifting) ext finite_keys)
  also have "\<dots> =
    (if I + J \<in> ?S
      then coeff P (I + J) * of_nat (pjet_mchoose (I + J) J)
      else 0)"
    by (simp add: pjet_hasse_monom_coeff_exact)
  also have "\<dots> =
    coeff P (I + J) * of_nat (pjet_mchoose (I + J) J)"
    by (auto simp: pjet_hasse_monom_coeff_exact coeff_def in_keys_iff)
  finally show ?thesis .
qed

lemma pjet_mchoose_on_set:
  assumes fin: "finite S"
    and supp: "Poly_Mapping.keys K \<union> Poly_Mapping.keys J \<subseteq> S"
  shows "pjet_mchoose K J = (\<Prod>v\<in>S. Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v)" (is "?lhs = ?rhs")
proof -
  have "(\<Prod>v\<in>Poly_Mapping.keys K \<union> Poly_Mapping.keys J. Poly_Mapping.lookup K v choose Poly_Mapping.lookup J v) = ?rhs"
    by (intro prod.mono_neutral_left[OF fin supp])
      (auto simp: not_in_keys_iff_lookup_eq_zero)
  then show ?thesis by (simp only: pjet_mchoose_def)
qed

lemma pjet_choose_comp_scalar:
  "(k+i+j choose j) * (k+i choose i) = (i+j choose i) * (k+i+j choose i+j)"
  using choose_mult[of j "i+j" "k+i+j"]  binomial_symmetric[of j "i+j"] by (simp add: algebra_simps)

lemma pjet_mchoose_comp:
  fixes K I J :: "nat \<Rightarrow>\<^sub>0 nat"
  shows "pjet_mchoose (K+I+J) J * pjet_mchoose (K+I) I =
    pjet_mchoose (I+J) I * pjet_mchoose (K+I+J) (I+J)"
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
  have e1: "pjet_mchoose (K+I+J) J =
    (\<Prod>v\<in>?S. Poly_Mapping.lookup (K+I+J) v choose
      Poly_Mapping.lookup J v)"
    by (rule pjet_mchoose_on_set[OF fin]) (use kij in auto)
  have e2: "pjet_mchoose (K+I) I =
    (\<Prod>v\<in>?S. Poly_Mapping.lookup (K+I) v choose
      Poly_Mapping.lookup I v)"
    by (rule pjet_mchoose_on_set[OF fin]) (use ki in auto)
  have e3: "pjet_mchoose (I+J) I =
    (\<Prod>v\<in>?S. Poly_Mapping.lookup (I+J) v choose
      Poly_Mapping.lookup I v)"
    by (rule pjet_mchoose_on_set[OF fin]) (use ij in auto)
  have e4: "pjet_mchoose (K+I+J) (I+J) =
    (\<Prod>v\<in>?S. Poly_Mapping.lookup (K+I+J) v choose
      Poly_Mapping.lookup (I+J) v)"
    by (rule pjet_mchoose_on_set[OF fin]) (use kij ij in auto)
  show ?thesis
    unfolding e1 e2 e3 e4 prod.distrib [symmetric]
    by (simp add: lookup_add pjet_choose_comp_scalar)
qed

lemma pjet_hasse_comp:
  fixes P :: "'a::idom mpoly"
  shows "pjet_hasse I (pjet_hasse J P) =
    Const (of_nat (pjet_mchoose (I+J) I)) *
      pjet_hasse (I+J) P"
proof -
  have ce: "coeff (pjet_hasse I (pjet_hasse J P)) K =
    coeff (Const (of_nat (pjet_mchoose (I+J) I)) *
      pjet_hasse (I+J) P) K" for K
  proof -
    have lhs: "coeff (pjet_hasse I (pjet_hasse J P)) K =
      coeff P (K+I+J) *
        of_nat (pjet_mchoose (K+I+J) J) *
        of_nat (pjet_mchoose (K+I) I)"
      by (simp add: pjet_hasse_coeff_exact add.assoc)
    have rhs: "coeff (Const (of_nat (pjet_mchoose (I+J) I)) *
        pjet_hasse (I+J) P) K =
      of_nat (pjet_mchoose (I+J) I) *
        (coeff P (K+I+J) *
          of_nat (pjet_mchoose (K+I+J) (I+J)))"
      by (simp add: pjet_coeff_Const_mult pjet_hasse_coeff_exact
        add.assoc)
    show ?thesis using lhs rhs pjet_mchoose_comp[of K I J]
      by (simp add: algebra_simps flip: of_nat_mult)
  qed
  show ?thesis using ce
    by (simp add: coeff_eq[symmetric] fun_eq_iff)
qed


section \<open>Scalar coefficients and support boxes\<close>

lemma pjet_coeff_smult_rat:
  fixes P :: "rat mpoly"
  shows "coeff (smult d P) I = d * coeff P I"
  by (simp add: coeff_def smult.rep_eq Poly_Mapping.map.rep_eq when_def)

lemma pjet_hasse_coeff_support:
  fixes P :: "'a::idom mpoly"
  assumes nz: "coeff (pjet_hasse J P) I \<noteq> 0"
  shows "coeff P (I + J) \<noteq> 0"
  using nz by (auto simp: pjet_hasse_coeff_exact)

lemma pjet_poly_in_box_mono:
  fixes P :: "'a::comm_ring_1 mpoly"
  assumes box: "pjet_poly_in_box m r P"
    and le: "\<forall>v<m. r v \<le> s v"
  shows "pjet_poly_in_box m s P"
  unfolding pjet_poly_in_box_def
proof (intro subsetI)
  fix I
  assume "I \<in> Poly_Mapping.keys (mapping_of P)"
  then have ib: "I \<in> pjet_exponent_box m r"
    using box by (auto simp: pjet_poly_in_box_def)
  show "I \<in> pjet_exponent_box m s"
    using ib le by (auto simp: pjet_exponent_box_iff intro: order_trans)
qed

lemma pjet_hasse_in_box:
  fixes P :: "'a::idom mpoly"
  assumes box: "pjet_poly_in_box m r P"
  shows "pjet_poly_in_box m (\<lambda>v. r v - Poly_Mapping.lookup I v) (pjet_hasse I P)"
  unfolding pjet_poly_in_box_def
proof (intro subsetI)
  fix K
  assume "K \<in> Poly_Mapping.keys (mapping_of (pjet_hasse I P))"
  then have c: "coeff (pjet_hasse I P) K \<noteq> 0"
    by (simp add: coeff_def in_keys_iff)
  have cp: "coeff P (K + I) \<noteq> 0"
    by (rule pjet_hasse_coeff_support[OF c])
  have orig: "K + I \<in> pjet_exponent_box m r"
    using box cp by (auto simp: pjet_poly_in_box_def coeff_def in_keys_iff)
  have orig_vars: "Poly_Mapping.keys (K + I) \<subseteq> {..<m}"
    by (rule pjet_exponent_boxD(1)[OF orig])
  show "K \<in> pjet_exponent_box m
    (\<lambda>v. r v - Poly_Mapping.lookup I v)"
  proof (rule pjet_exponent_boxI)
    show "Poly_Mapping.keys K \<subseteq> {..<m}"
      using keys_plus_ninv_comm_monoid_add orig_vars by fastforce
    fix v
    assume vm: "v < m"
    have "Poly_Mapping.lookup (K + I) v \<le> r v"
      by (rule pjet_exponent_boxD(2)[OF orig vm])
    then show "Poly_Mapping.lookup K v \<le> r v - Poly_Mapping.lookup I v"
      by (simp add: lookup_add)
  qed
qed

lemma pjet_hasse_preserves_box:
  fixes P :: "'a::idom mpoly"
  assumes box: "pjet_poly_in_box m r P"
  shows "pjet_poly_in_box m r (pjet_hasse J P)"
  by (rule pjet_poly_in_box_mono[OF pjet_hasse_in_box[OF box]]) simp


end
