theory Roth_Hasse_Derivative
  imports Roth_Disjoint_Index
begin

section \<open>Polynomial Hasse derivatives\<close>

lemma roth_replace_coeff_mult:
  fixes f :: "'a::comm_ring_1 \<Rightarrow> 'b::comm_ring_1"
  assumes h0: "f 0 = 0"
    and hadd: "\<And>x y. f (x + y) = f x + f y"
    and hmul: "\<And>x y. f (x * y) = f x * f y"
  shows "replace_coeff f (P * Q) =
    replace_coeff f P * replace_coeff f Q"
proof (induction P rule: mpoly_induct)
  case (monom m c)
  then show ?case
  proof (induction Q rule: mpoly_induct)
    case (monom n d)
    then show ?case
      by (simp add: mult_monom replace_coeff_monom h0 hmul)
  next
    case (sum q1 q2 n d)
    then show ?case
      by (simp add: algebra_simps replace_coeff_add h0 hadd)
  qed
next
  case (sum p1 p2 m c)
  then show ?case
    by (simp add: algebra_simps replace_coeff_add h0 hadd)
qed

lemma roth_replace_coeff_one:
  fixes f :: "'a::comm_ring_1 \<Rightarrow> 'b::comm_ring_1"
  assumes h0: "f 0 = 0" and h1: "f 1 = 1"
  shows "replace_coeff f 1 = 1"
  using replace_coeff_monom[of f 0 1] by (simp add: h0 h1)

lemma roth_replace_coeff_zero:
  assumes "f 0 = 0"
  shows "replace_coeff f 0 = 0"
  using replace_coeff_monom[of f 0 0] assms by simp

lemma roth_replace_coeff_sum:
  fixes f :: "'a::comm_ring_1 \<Rightarrow> 'b::comm_ring_1"
  assumes fin: "finite S" and h0: "f 0 = 0"
    and hadd: "\<And>x y. f (x + y) = f x + f y"
  shows "replace_coeff f (\<Sum>x\<in>S. P x) =
    (\<Sum>x\<in>S. replace_coeff f (P x))"
  using fin by (induction S rule: finite_induct)
    (simp_all add: roth_replace_coeff_zero replace_coeff_add h0 hadd)

lemma roth_replace_coeff_power:
  fixes f :: "'a::comm_ring_1 \<Rightarrow> 'b::comm_ring_1"
  assumes h0: "f 0 = 0" and h1: "f 1 = 1"
    and hadd: "\<And>x y. f (x + y) = f x + f y"
    and hmul: "\<And>x y. f (x * y) = f x * f y"
  shows "replace_coeff f (P ^ n) = replace_coeff f P ^ n"
  by (induction n)
    (simp_all add: roth_replace_coeff_one[OF h0 h1]
      roth_replace_coeff_mult[OF h0 hadd hmul])

lemma roth_replace_coeff_prod:
  fixes f :: "'a::comm_ring_1 \<Rightarrow> 'b::comm_ring_1"
  assumes fin: "finite S" and h0: "f 0 = 0" and h1: "f 1 = 1"
    and hadd: "\<And>x y. f (x + y) = f x + f y"
    and hmul: "\<And>x y. f (x * y) = f x * f y"
  shows "replace_coeff f (\<Prod>x\<in>S. P x) =
    (\<Prod>x\<in>S. replace_coeff f (P x))"
  using fin by (induction S rule: finite_induct)
    (simp_all add: roth_replace_coeff_one[OF h0 h1]
      roth_replace_coeff_mult[OF h0 hadd hmul])

lemma roth_replace_coeff_comp:
  assumes f0: "f 0 = 0" and g0: "g 0 = 0"
  shows "replace_coeff g (replace_coeff f P) =
    replace_coeff (g \<circ> f) P"
  by (simp add: coeff_eq[symmetric] fun_eq_iff
    coeff_replace_coeff f0 g0)

lemma roth_replace_coeff_id [simp]:
  "replace_coeff id P = P"
  by (simp add: coeff_eq[symmetric] fun_eq_iff
    coeff_replace_coeff)

lemma roth_Const_monom:
  "Const c = monom 0 c"
  by (simp add: mapping_of_inject[symmetric] Const.rep_eq
    Const\<^sub>0_def monom.rep_eq)

lemma roth_Const_mult:
  "Const (x * y) = (Const x :: 'a::comm_ring_1 mpoly) * Const y"
  by (simp add: roth_Const_monom mult_monom)

lemma roth_Const_monom_left:
  "Const a * monom K b = monom K (a * b)"
  by (simp add: roth_Const_monom mult_monom)

lemma roth_Const_monom_right:
  "monom K a * Const b = monom K (a * b)"
  by (simp add: roth_Const_monom mult_monom)

lemma roth_coeff_Const_mult:
  "coeff (Const c * Q) I = c * coeff Q I"
  using coeff_monom_mult[of 0 c Q I]
  by (simp add: roth_Const_monom)

lemma roth_Const_one [simp]:
  "Const (1::'a::comm_ring_1) = 1"
  by (simp add: roth_Const_monom)

lemma roth_Const_power:
  "Const (c::'a::comm_ring_1) ^ n = Const (c ^ n)"
  by (induction n) (simp_all add: power_Suc roth_Const_mult)

lemma roth_of_nat_Const:
  "(of_nat n :: 'a::comm_ring_1 mpoly) = Const (of_nat n)"
  by (induction n) (simp_all add: roth_Const_add)

lemma roth_replace_coeff_Const:
  assumes "f 0 = 0"
  shows "replace_coeff f (Const c) = Const (f c)"
  by (simp add: roth_Const_monom replace_coeff_monom assms)

lemma roth_Var_monom:
  "Var v = monom (Poly_Mapping.single v 1) (1::'a::comm_ring_1)"
  by (simp add: mapping_of_inject[symmetric] Var.rep_eq
    Var\<^sub>0_def monom.rep_eq)

lemma roth_Var_power:
  "(Var v :: 'a::comm_ring_1 mpoly) ^ n =
    monom (Poly_Mapping.single v n) 1"
  by (induction n)
    (simp_all add: power_Suc roth_Const_monom
      roth_Var_monom mult_monom
      Poly_Mapping.single_add[symmetric])

lemma roth_binomial_outer_term:
  fixes x :: "'a::comm_ring_1 mpoly"
  shows "(of_nat (n choose k) :: 'a mpoly mpoly) *
    (Var v)^k * (Const x)^(n-k) =
    monom (Poly_Mapping.single v k)
      (of_nat (n choose k) * x^(n-k))"
proof -
  have a: "(of_nat (n choose k) :: 'a mpoly mpoly) =
    Const (of_nat (n choose k) :: 'a mpoly)"
    by (rule roth_of_nat_Const)
  have b: "(Var v :: 'a mpoly mpoly)^k =
    monom (Poly_Mapping.single v k) 1"
    by (rule roth_Var_power)
  have c: "(Const x :: 'a mpoly mpoly)^(n-k) = Const (x^(n-k))"
    by (rule roth_Const_power)
  have algebra:
    "Const (of_nat (n choose k) :: 'a mpoly) *
      monom (Poly_Mapping.single v k) 1 *
      Const (x^(n-k)) =
      monom (Poly_Mapping.single v k)
        (of_nat (n choose k) * x^(n-k))"
    by (simp only: roth_Const_monom_left
      roth_Const_monom_right) simp
  show ?thesis by (simp only: a b c algebra)
qed

lemma roth_shift_Var_power:
  fixes x :: "'a::comm_ring_1 mpoly"
  shows "(Var v + Const x)^n =
    (\<Sum>k\<le>n. monom (Poly_Mapping.single v k)
      (of_nat (n choose k) * x^(n-k)))"
  by (simp only: binomial_ring roth_binomial_outer_term)

lemma roth_coeff_sum:
  assumes "finite S"
  shows "coeff (\<Sum>x\<in>S. P x) I = (\<Sum>x\<in>S. coeff (P x) I)"
  using assms by (induction S rule: finite_induct)
    (simp_all add: coeff_def zero_mpoly.rep_eq
      plus_mpoly.rep_eq lookup_add)

lemma roth_coeff_shift_Var_power:
  fixes x :: "'a::comm_ring_1 mpoly"
  shows "coeff ((Var v + Const x)^n) I =
    (\<Sum>k\<le>n. (of_nat (n choose k) * x^(n-k))
      when I = Poly_Mapping.single v k)"
  by (simp only: roth_shift_Var_power
    roth_coeff_sum[OF finite_atMost] coeff_monom)

lemma roth_single_inj:
  "Poly_Mapping.single v i = Poly_Mapping.single v j \<longleftrightarrow> i = j"
  by (metis Poly_Mapping.lookup_single_eq)

lemma roth_replace_coeff_Var:
  fixes f :: "'a::comm_ring_1 \<Rightarrow> 'b::comm_ring_1"
  assumes f0: "f 0 = 0" and f1: "f 1 = 1"
  shows "replace_coeff f (Var v) = Var v"
  unfolding roth_Var_monom
  using replace_coeff_monom[of f "Poly_Mapping.single v 1" 1]
    f0 f1 by simp

lemma roth_insertion_Const [simp]:
  "insertion a (Const c) = c"
  using insertion_single[of a 0 0 c]
  by (simp add: roth_Const_monom)

lemma roth_insertion_Var [simp]:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
  shows "insertion a (Var v) = a v"
  unfolding roth_Var_monom
  using insertion_single[of a v 1 1] by simp

lemma roth_insertion_power:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
    and P :: "'a mpoly"
  shows "insertion a (P ^ n) = insertion a P ^ n"
  by (induction n) (simp_all add: insertion_mult)

lemma roth_insertion_prod:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
    and P :: "'i \<Rightarrow> 'a mpoly"
  assumes "finite S"
  shows "insertion a (\<Prod>x\<in>S. P x) =
    (\<Prod>x\<in>S. insertion a (P x))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: insertion_mult)

lemma roth_insertion_sum:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
    and P :: "'i \<Rightarrow> 'a mpoly"
  assumes "finite S"
  shows "insertion a (\<Sum>x\<in>S. P x) =
    (\<Sum>x\<in>S. insertion a (P x))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: insertion_add)

lemma roth_insertion_monom:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
  shows "insertion a (monom I c) =
    c * (\<Prod>v\<in>Poly_Mapping.keys I.
      a v ^ Poly_Mapping.lookup I v)"
  using roth_mpoly_subst_monom[of Var I c]
  by (simp add: insertion_mult roth_insertion_prod
    roth_insertion_power)

lemma roth_insertion_sum_any:
  fixes b :: "nat \<Rightarrow> 'a::comm_ring_1"
    and T :: "'i \<Rightarrow> 'a mpoly"
  assumes "finite S"
  shows "insertion b (\<Sum>x\<in>S. T x) =
    (\<Sum>x\<in>S. insertion b (T x))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: insertion_add)

lemma roth_insertion_prod_any:
  fixes b :: "nat \<Rightarrow> 'a::comm_ring_1"
    and T :: "'i \<Rightarrow> 'a mpoly"
  assumes "finite S"
  shows "insertion b (\<Prod>x\<in>S. T x) =
    (\<Prod>x\<in>S. insertion b (T x))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: insertion_mult)

lemma roth_insertion_power_any:
  fixes b :: "nat \<Rightarrow> 'a::comm_ring_1"
  shows "insertion b (P ^ n) = insertion b P ^ n"
  by (induction n) (simp_all add: insertion_mult)

lemma roth_insertion_monom_any:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1" and c :: 'a
  shows "insertion a (MPoly_Type.monom I c) =
    c * (\<Prod>v\<in>Poly_Mapping.keys I. a v ^ Poly_Mapping.lookup I v)"
  using roth_mpoly_subst_monom[of Var I c]
  by (simp add: insertion_mult roth_insertion_prod_any
    roth_insertion_power_any)

lemma roth_insertion_subst:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
    and g :: "nat \<Rightarrow> 'a mpoly"
  shows "insertion a (roth_mpoly_subst g P) =
    insertion (\<lambda>v. insertion a (g v)) P"
proof (induction P rule: mpoly_induct)
  case (monom I c)
  then show ?case
    by (simp add: roth_mpoly_subst_monom roth_insertion_monom
      roth_insertion_prod roth_insertion_power insertion_mult)
next
  case (sum P Q I c)
  then show ?case
    by (simp add: roth_mpoly_subst_add insertion_add)
qed

lemma roth_coeff_shift_zero:
  fixes c :: "'a::comm_ring_1"
  shows "coeff (Var v + Const c) 0 = c"
proof -
  have "coeff (Var v + Const c) 0 =
    insertion (\<lambda>_. 0) (Var v + Const c)"
    by simp
  also have "\<dots> = c"
    by (simp only: insertion_add roth_insertion_Var
      roth_insertion_Const add_0)
  finally show ?thesis .
qed

lemma roth_taylor_coeff_zero:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
  shows "roth_taylor_coeff a 0 P = insertion a P"
proof -
  have "roth_taylor_coeff a 0 P =
    insertion (\<lambda>_. 0) (roth_translate a P)"
    by (simp add: roth_taylor_coeff_def)
  also have "\<dots> =
    insertion (\<lambda>v. insertion (\<lambda>_. 0)
      (Var v + Const (a v))) P"
    by (simp only: roth_translate_def roth_insertion_subst)
  also have "\<dots> = insertion a P"
    by (simp add: roth_coeff_shift_zero)
  finally show ?thesis .
qed

lemma roth_replace_coeff_subst:
  fixes h :: "'a::comm_ring_1 \<Rightarrow> 'b::comm_ring_1"
  assumes h0: "h 0 = 0" and h1: "h 1 = 1"
    and hadd: "\<And>x y. h (x + y) = h x + h y"
    and hmul: "\<And>x y. h (x * y) = h x * h y"
  shows "replace_coeff h (roth_mpoly_subst g P) =
    roth_mpoly_subst (\<lambda>v. replace_coeff h (g v))
      (replace_coeff h P)"
proof (induction P rule: mpoly_induct)
  case (monom I c)
  then show ?case
    by (simp add: roth_mpoly_subst_monom roth_replace_coeff_mult
      roth_replace_coeff_Const roth_replace_coeff_prod
      roth_replace_coeff_power replace_coeff_monom
      h0 h1 hadd hmul)
next
  case (sum P Q I c)
  then show ?case
    by (simp add: roth_mpoly_subst_add
      replace_coeff_add h0 hadd)
qed

definition roth_lift ::
  "'a::comm_ring_1 mpoly \<Rightarrow> 'a mpoly mpoly" where
  "roth_lift P = replace_coeff Const P"

lemma roth_lift_Const:
  "roth_lift (Const c) = Const (Const c)"
  by (simp add: roth_lift_def roth_replace_coeff_Const)

lemma roth_lift_Var:
  "roth_lift (Var v) = Var v"
  by (simp add: roth_lift_def roth_replace_coeff_Var)

lemma roth_lift_zero [simp]:
  "roth_lift 0 = 0"
  using replace_coeff_monom[of Const 0 0]
  by (simp add: roth_lift_def roth_Const_zero)

lemma roth_lift_add:
  "roth_lift (P + Q) = roth_lift P + roth_lift Q"
  by (simp add: roth_lift_def replace_coeff_add
    roth_Const_add roth_Const_zero)

lemma roth_lift_mult:
  "roth_lift (P * Q) = roth_lift P * roth_lift Q"
  by (simp add: roth_lift_def roth_replace_coeff_mult
    roth_Const_zero roth_Const_add[symmetric]
    roth_Const_mult[symmetric])

lemma roth_lift_one [simp]:
  "roth_lift 1 = 1"
  by (simp add: roth_lift_def roth_replace_coeff_one)

lemma roth_lift_power:
  "roth_lift (P ^ n) = roth_lift P ^ n"
  by (induction n) (simp_all add: roth_lift_mult)

lemma roth_lift_eval:
  "replace_coeff (insertion a) (roth_lift P) = P"
proof -
  have eq: "insertion a \<circ> Const = id"
    by (rule ext) simp
  show ?thesis
    by (simp add: roth_lift_def roth_replace_coeff_comp
      roth_Const_zero eq)
qed

lemma roth_lift_insertion_Var:
  "insertion Var (roth_lift P) = P"
proof (induction P rule: mpoly_induct)
  case (monom I c)
  have lift: "roth_lift (monom I c) = monom I (Const c)"
    by (simp add: roth_lift_def replace_coeff_monom
      roth_Const_zero)
  have poly: "monom I c =
    Const c * (\<Prod>v\<in>Poly_Mapping.keys I.
      Var v ^ Poly_Mapping.lookup I v)"
    using roth_mpoly_subst_monom[of Var I c] by simp
  have lhs: "insertion Var (roth_lift (monom I c)) =
    Const c * (\<Prod>v\<in>Poly_Mapping.keys I.
      Var v ^ Poly_Mapping.lookup I v)"
    by (simp only: lift roth_insertion_monom)
  show ?case using lhs poly by simp
next
  case (sum P Q I c)
  then show ?case
    by (simp add: roth_lift_add insertion_add)
qed

lemma roth_eval_shift:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
  shows "replace_coeff (insertion a) (Var v + Const (Var v)) =
    Var v + Const (a v)"
  by (simp add: replace_coeff_add roth_replace_coeff_Var
    roth_replace_coeff_Const insertion_add)

lemma roth_eval_translate:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
  shows "replace_coeff (insertion a)
    (roth_translate Var (roth_lift P)) = roth_translate a P"
  by (simp add: roth_translate_def roth_replace_coeff_subst
    insertion_add insertion_mult roth_lift_eval roth_eval_shift)

lemma roth_translate_Const [simp]:
  "roth_translate a (Const c) = Const c"
  by (simp add: roth_translate_def)

lemma roth_translate_Var [simp]:
  "roth_translate a (Var v) = Var v + Const (a v)"
  by (simp add: roth_translate_def)

lemma roth_translate_one [simp]:
  "roth_translate a 1 = 1"
  using roth_translate_Const[of a 1] by simp

lemma roth_translate_power:
  "roth_translate a (P ^ n) = roth_translate a P ^ n"
  by (induction n) (simp_all add: roth_translate_mult)

lemma roth_translate_zero_poly [simp]:
  "roth_translate a 0 = 0"
  by (simp add: roth_translate_def)

lemma roth_lift_translate:
  "roth_lift (roth_translate a P) =
    roth_translate (\<lambda>v. Const (a v)) (roth_lift P)"
  by (simp add: roth_lift_def roth_translate_def
    roth_replace_coeff_subst roth_replace_coeff_Var
    roth_replace_coeff_Const replace_coeff_add
    roth_Const_add roth_Const_mult)

lemma roth_lift_translate_coeff:
  "replace_coeff (roth_translate a) (roth_lift P) =
    roth_lift P"
proof -
  have eq: "roth_translate a \<circ> Const = Const"
    by (rule ext) simp
  show ?thesis
    by (simp add: roth_lift_def roth_replace_coeff_comp eq)
qed

lemma roth_translate_shift_coeff:
  "replace_coeff (roth_translate a)
    (Var v + Const (Var v)) =
    Var v + Const (Var v + Const (a v))"
  by (simp add: replace_coeff_add roth_replace_coeff_Var
    roth_replace_coeff_Const roth_translate_add)

lemma roth_translate_coeff_commute:
  "replace_coeff (roth_translate a)
    (roth_translate Var (roth_lift P)) =
    roth_translate Var (roth_lift (roth_translate a P))"
proof -
  have nat: "replace_coeff (roth_translate a)
      (roth_mpoly_subst (\<lambda>v. Var v + Const (Var v))
        (roth_lift P)) =
    roth_mpoly_subst
      (\<lambda>v. replace_coeff (roth_translate a)
        (Var v + Const (Var v)))
      (replace_coeff (roth_translate a) (roth_lift P))"
    by (rule roth_replace_coeff_subst)
      (simp_all add: roth_translate_add roth_translate_mult)
  have "replace_coeff (roth_translate a)
      (roth_translate Var (roth_lift P)) =
    roth_translate (\<lambda>v. Var v + Const (a v))
      (roth_lift P)"
    using nat by (simp add: roth_translate_def
      roth_translate_shift_coeff roth_lift_translate_coeff)
  also have "\<dots> =
    roth_translate Var (roth_lift (roth_translate a P))"
    by (simp add: roth_lift_translate roth_translate_comp)
  finally show ?thesis .
qed

definition roth_hasse ::
  "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>
    'a::comm_ring_1 mpoly \<Rightarrow> 'a mpoly" where
  "roth_hasse I P = roth_taylor_coeff Var I (roth_lift P)"

lemma roth_hasse_zero [simp]:
  "roth_hasse 0 P = P"
  by (simp add: roth_hasse_def roth_taylor_coeff_zero
    roth_lift_insertion_Var)

lemma roth_hasse_Const:
  "roth_hasse I (Const c) = (if I = 0 then Const c else 0)"
proof -
  have "roth_hasse I (Const c) = coeff (Const (Const c)) I"
    by (simp only: roth_hasse_def roth_taylor_coeff_def
      roth_lift_Const roth_translate_Const)
  then show ?thesis
    by (simp add: roth_Const_monom coeff_monom when_def)
qed

lemma roth_hasse_Var:
  "roth_hasse I (Var v :: 'a::comm_ring_1 mpoly) =
    (if I = 0 then Var v
      else if I = Poly_Mapping.single v 1 then 1 else 0)"
proof -
  have base: "roth_hasse I (Var v :: 'a mpoly) =
    coeff (Var v + Const (Var v)) I"
    by (simp only: roth_hasse_def roth_taylor_coeff_def
      roth_lift_Var roth_translate_Var)
  have var_coeff:
    "coeff (Var v + Const (Var v :: 'a mpoly)) I =
      (if I = 0 then Var v
        else if I = Poly_Mapping.single v 1 then 1 else 0)"
  proof (cases "I = 0")
    case True
    then show ?thesis by (simp add: roth_coeff_shift_zero)
  next
    case False
    then show ?thesis
      by (simp add: coeff_add[symmetric] roth_Var_monom
        roth_Const_monom coeff_monom when_def)
  qed
  show ?thesis by (simp only: base var_coeff)
qed

lemma roth_hasse_Var_power:
  "roth_hasse I ((Var v :: 'a::comm_ring_1 mpoly) ^ n) =
    coeff ((Var v + Const (Var v)) ^ n) I"
  by (simp only: roth_hasse_def roth_taylor_coeff_def
    roth_lift_power roth_lift_Var roth_translate_power
    roth_translate_Var)

lemma roth_hasse_Var_power_expansion:
  "roth_hasse I ((Var v :: 'a::comm_ring_1 mpoly) ^ n) =
    (\<Sum>k\<le>n. (of_nat (n choose k) * Var v^(n-k))
      when I = Poly_Mapping.single v k)"
  by (simp only: roth_hasse_Var_power roth_coeff_shift_Var_power)

lemma roth_hasse_Var_power_single:
  "roth_hasse (Poly_Mapping.single v i)
    ((Var v :: 'a::comm_ring_1 mpoly) ^ n) =
    (if i \<le> n then of_nat (n choose i) * Var v^(n-i) else 0)"
  by (simp add: roth_hasse_Var_power_expansion
    roth_single_inj when_def sum.If_cases)

lemma roth_hasse_Var_power_index_support:
  fixes v :: nat
  assumes "roth_hasse J ((Var v :: 'a::comm_ring_1 mpoly)^n) \<noteq> 0"
  obtains k where "k \<le> n" "J = Poly_Mapping.single v k"
proof -
  have "\<exists>k\<le>n. J = Poly_Mapping.single v k"
  proof (rule ccontr)
    assume "\<not> (\<exists>k\<le>n. J = Poly_Mapping.single v k)"
    then have "roth_hasse J ((Var v :: 'a mpoly)^n) = 0"
      by (simp add: roth_hasse_Var_power_expansion when_def)
    then show False using assms by simp
  qed
  then show ?thesis using that by blast
qed

lemma roth_hasse_Var_power_diagonal:
  fixes v :: nat
  assumes c: "coeff (roth_hasse J
    ((Var v :: 'a::comm_ring_1 mpoly)^n)) I \<noteq> 0"
  shows "I + J = Poly_Mapping.single v n"
proof -
  have nz: "roth_hasse J ((Var v :: 'a mpoly)^n) \<noteq> 0"
    using c by (auto simp: coeff_def zero_mpoly.rep_eq)
  obtain k where kn: "k \<le> n"
    and j: "J = Poly_Mapping.single v k"
    using roth_hasse_Var_power_index_support[OF nz] by blast
  have d: "roth_hasse J ((Var v :: 'a mpoly)^n) =
    of_nat (n choose k) * Var v^(n-k)"
    using roth_hasse_Var_power_single[of v k n] kn j by simp
  have ce: "coeff (roth_hasse J
      ((Var v :: 'a mpoly)^n)) I =
    of_nat (n choose k) *
      coeff ((Var v :: 'a mpoly)^(n-k)) I"
    by (simp only: d roth_of_nat_Const roth_coeff_Const_mult)
  have factor: "of_nat (n choose k) *
    coeff ((Var v :: 'a mpoly)^(n-k)) I \<noteq> 0"
    using c ce by metis
  have cv: "coeff ((Var v :: 'a mpoly)^(n-k)) I \<noteq> 0"
    using factor by auto
  have i: "I = Poly_Mapping.single v (n-k)"
    using cv by (auto simp: roth_Var_power coeff_monom when_def
      split: if_splits)
  show ?thesis
    using i j kn
    by (simp add: Poly_Mapping.single_add[symmetric])
qed

lemma roth_hasse_add:
  "roth_hasse I (P + Q) = roth_hasse I P + roth_hasse I Q"
  by (simp add: roth_hasse_def roth_lift_add roth_taylor_coeff_add)

lemma roth_hasse_zero_poly [simp]:
  "roth_hasse I (0::'a::comm_ring_1 mpoly) = 0"
  by (simp add: roth_hasse_def roth_taylor_coeff_def
    roth_translate_zero_poly coeff_def zero_mpoly.rep_eq)

lemma roth_hasse_sum:
  assumes "finite S"
  shows "roth_hasse I (\<Sum>x\<in>S. P x) =
    (\<Sum>x\<in>S. roth_hasse I (P x))"
  using assms by (induction S rule: finite_induct)
    (simp_all add: roth_hasse_add)

lemma roth_hasse_smul:
  "roth_hasse I (Const c * P) = Const c * roth_hasse I P"
proof -
  have t: "roth_translate Var (roth_lift (Const c * P)) =
    Const (Const c) * roth_translate Var (roth_lift P)"
    by (simp only: roth_lift_mult roth_lift_Const
      roth_translate_mult roth_translate_Const)
  show ?thesis
    by (simp only: roth_hasse_def roth_taylor_coeff_def
      t roth_coeff_Const_mult)
qed

lemma roth_monom_smul:
  "monom K (c::'a::comm_ring_1) = Const c * monom K 1"
  by (simp add: roth_Const_monom mult_monom)

lemma roth_hasse_monom_smul:
  "roth_hasse I (monom K (c::'a::comm_ring_1)) =
    Const c * roth_hasse I (monom K 1)"
proof -
  have e: "monom K c = Const c * monom K 1"
    by (rule roth_monom_smul)
  have "roth_hasse I (monom K c) =
    roth_hasse I (Const c * monom K 1)"
    using e by simp
  also have "\<dots> = Const c * roth_hasse I (monom K 1)"
    by (rule roth_hasse_smul)
  finally show ?thesis .
qed

lemma roth_hasse_mult:
  "roth_hasse I (P * Q) =
    (\<Sum>J. roth_hasse J P *
      (\<Sum>K. roth_hasse K Q when I = J + K))"
  by (simp add: roth_hasse_def roth_lift_mult
    roth_taylor_coeff_mult)

lemma roth_hasse_eval:
  fixes a :: "nat \<Rightarrow> 'a::comm_ring_1"
  shows "insertion a (roth_hasse I P) =
    roth_taylor_coeff a I P"
proof -
  have h: "coeff (replace_coeff (insertion a)
      (roth_translate Var (roth_lift P))) I =
    insertion a
      (coeff (roth_translate Var (roth_lift P)) I)"
    by (simp add: coeff_replace_coeff)
  show ?thesis
    using h by (simp only: roth_hasse_def
      roth_taylor_coeff_def roth_eval_translate)
qed

lemma roth_hasse_origin:
  fixes P :: "'a::comm_ring_1 mpoly"
  shows "insertion (\<lambda>_. 0) (roth_hasse I P) = coeff P I"
  by (simp only: roth_hasse_eval roth_taylor_coeff_def
    roth_translate_zero)

lemma roth_hasse_translate:
  "roth_hasse I (roth_translate a P) =
    roth_translate a (roth_hasse I P)"
proof -
  have h: "coeff (replace_coeff (roth_translate a)
      (roth_translate Var (roth_lift P))) I =
    roth_translate a
      (coeff (roth_translate Var (roth_lift P)) I)"
    by (rule coeff_replace_coeff) simp
  show ?thesis
    using h roth_translate_coeff_commute[of a P]
    by (simp only: roth_hasse_def roth_taylor_coeff_def)
qed

lemma roth_taylor_identity_hasse:
  "P = (\<Sum>I\<in>Poly_Mapping.keys (mapping_of (roth_translate a P)).
    Const (insertion a (roth_hasse I P)) *
      (\<Prod>v\<in>Poly_Mapping.keys I.
        (Var v - Const (a v)) ^ Poly_Mapping.lookup I v))"
  by (simp add: roth_taylor_identity_explicit roth_hasse_eval)

end
