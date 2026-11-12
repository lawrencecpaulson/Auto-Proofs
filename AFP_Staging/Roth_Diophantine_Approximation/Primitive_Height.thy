theory Primitive_Height
  imports
    Disjoint_Index
    "HOL.Transcendental"
    Hasse_Derivative
begin

section \<open>Heights at rational points\<close>

definition roth_rat_height :: "rat \<Rightarrow> nat" where
  "roth_rat_height x =
    nat (max (abs (fst (quotient_of x))) (snd (quotient_of x)))"

definition roth_rat_log_height :: "rat \<Rightarrow> real" where
  "roth_rat_log_height x = ln (real (roth_rat_height x))"

lemma roth_rat_height_pos [simp]: "0 < roth_rat_height x"
  using quotient_of_denom_pos'[of x]
  by (simp add: roth_rat_height_def)

lemma roth_rat_height_ge_one [simp]: "1 \<le> roth_rat_height x"
  using roth_rat_height_pos[of x] by (simp only: Suc_le_eq)

lemma roth_rat_log_height_nonneg [simp]:
  "0 \<le> roth_rat_log_height x"
  using roth_rat_height_ge_one[of x]
  by (simp add: roth_rat_log_height_def)

lemma roth_rat_height_Fract:
  assumes "q > 0" "coprime p q"
  shows "roth_rat_height (Fract p q) = nat (max (abs p) q)"
  using assms by (simp add: roth_rat_height_def quotient_of_Fract)

lemma roth_rat_log_height_Fract:
  assumes "q > 0" "coprime p q"
  shows "roth_rat_log_height (Fract p q) =
    ln (real (nat (max (abs p) q)))"
  using roth_rat_height_Fract[OF assms]
  by (simp add: roth_rat_log_height_def)

section \<open>Coefficient sup norm\<close>

definition roth_int_coeff_sup :: "int mpoly \<Rightarrow> nat" where
  "roth_int_coeff_sup P =
    Max (insert 1 ((\<lambda>c. nat (abs c)) ` coeffs P))"

lemma roth_int_coeff_sup_pos [simp]: "0 < roth_int_coeff_sup P"
proof -
  have h: "1 \<le> Max (insert 1 ((\<lambda>c. nat (abs c)) ` coeffs P))"
    by (rule Max_ge) simp_all
  show ?thesis using h
    unfolding roth_int_coeff_sup_def by linarith
qed

lemma roth_int_coeff_sup_ge_one [simp]:
  "1 \<le> roth_int_coeff_sup P"
  using roth_int_coeff_sup_pos[of P] by linarith

lemma roth_int_coeff_sup_coeff:
  "nat (abs (coeff P I)) \<le> roth_int_coeff_sup P"
proof (cases "coeff P I = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have key: "I \<in> Poly_Mapping.keys (mapping_of P)"
    by (simp add: coeff_def in_keys_iff)
  then have "coeff P I \<in> coeffs P"
    by (simp add: coeffs.rep_eq coeff_def)
  then have mem: "nat (abs (coeff P I)) \<in>
      insert 1 ((\<lambda>c. nat (abs c)) ` coeffs P)"
    by blast
  have "nat (abs (coeff P I)) \<le>
      Max (insert 1 ((\<lambda>c. nat (abs c)) ` coeffs P))"
    by (rule Max_ge) (use mem in simp_all)
  then show ?thesis by (simp add: roth_int_coeff_sup_def)
qed

section \<open>Projective polynomial height\<close>

definition roth_integral_rep ::
  "rat mpoly \<Rightarrow> int mpoly \<Rightarrow> bool" where
  "roth_integral_rep P Q \<longleftrightarrow>
    (\<exists>c::rat. c \<noteq> 0 \<and> replace_coeff of_int Q = smult c P)"

lemma roth_smult_smult:
  "smult a (smult b (P::rat mpoly)) = smult (a*b) P"
  by (simp add: smult_conv_mult mult.assoc mult_monom)

lemma roth_integral_rep_smult:
  assumes a: "a \<noteq> (0::rat)"
  shows "roth_integral_rep (smult a P) Q =
    roth_integral_rep P Q"
proof (rule iffI)
  assume rep: "roth_integral_rep (smult a P) Q"
  then obtain c :: rat where c: "c \<noteq> 0"
    and eq: "replace_coeff of_int Q = smult c (smult a P)"
    by (auto simp: roth_integral_rep_def)
  show "roth_integral_rep P Q"
    unfolding roth_integral_rep_def using a c eq
    by (intro exI[of _ "c*a"]) (simp add: roth_smult_smult)
next
  assume rep: "roth_integral_rep P Q"
  then obtain c :: rat where c: "c \<noteq> 0"
    and eq: "replace_coeff of_int Q = smult c P"
    by (auto simp: roth_integral_rep_def)
  show "roth_integral_rep (smult a P) Q"
    unfolding roth_integral_rep_def using a c eq
    by (intro exI[of _ "c/a"]) (simp add: roth_smult_smult)
qed

lemma roth_integral_rep_cast:
  "roth_integral_rep (replace_coeff of_int Q) Q"
  unfolding roth_integral_rep_def
  by (rule exI[of _ 1]) (simp add: smult_conv_mult)

section \<open>Clearing denominators\<close>

lemma roth_rat_clear_denominator:
  obtains d n::int where "d > 0" "(of_int d::rat) * x = of_int n"
proof -
  obtain n d :: int where q: "quotient_of x = (n,d)"
    by (cases "quotient_of x") auto
  have d: "d > 0" using quotient_of_denom_pos[OF q] .
  have x: "x = of_int n / of_int d" using quotient_of_div[OF q] .
  show thesis using that[OF d] x d by simp
qed

lemma roth_clear_monom:
  fixes x :: rat
  shows "\<exists>d::int. d > 0 \<and> (\<exists>Q::int mpoly.
    replace_coeff of_int Q = smult (of_int d) (monom I x))"
proof -
  obtain d n::int where d: "d > 0"
    and dn: "(of_int d::rat) * x = of_int n"
    by (rule roth_rat_clear_denominator)
  have eq: "replace_coeff of_int (monom I n) =
    smult (of_int d) (monom I x)"
    using dn by (simp add: replace_coeff_monom)
  show ?thesis using d eq by blast
qed

lemma roth_smult_add:
  fixes P Q :: "'a::comm_ring_1 mpoly"
  shows "smult a (P+Q) = smult a P + smult a Q"
  by (simp add: smult_conv_mult algebra_simps)

lemma roth_cast_smult:
  fixes P :: "int mpoly"
  shows "replace_coeff of_int (smult d P) =
    smult (of_int d::rat) (replace_coeff of_int P)"
  by (induction P rule: mpoly_induct)
    (simp_all add: replace_coeff_monom replace_coeff_add roth_smult_add)

lemma roth_clear_add:
  fixes P R :: "rat mpoly"
  assumes P: "\<exists>d::int. d>0 \<and> (\<exists>Q::int mpoly.
    replace_coeff of_int Q = smult (of_int d) P)"
    and R: "\<exists>e::int. e>0 \<and> (\<exists>S::int mpoly.
    replace_coeff of_int S = smult (of_int e) R)"
  shows "\<exists>f::int. f>0 \<and> (\<exists>T::int mpoly.
    replace_coeff of_int T = smult (of_int f) (P+R))"
proof -
  obtain d :: int and Q :: "int mpoly" where d: "d>0"
    and Q: "replace_coeff of_int Q = smult (of_int d) P"
    using P by blast
  obtain e :: int and S :: "int mpoly" where e: "e>0"
    and S: "replace_coeff of_int S = smult (of_int e) R"
    using R by blast
  have comp: "smult a (smult b (F::rat mpoly)) = smult (a*b) F"
    for a b F by (simp add: smult_conv_mult mult.assoc mult_monom)
  have eq: "replace_coeff of_int (smult e Q + smult d S) =
    smult (of_int (d*e)) (P+R)"
    using Q S
    by (simp add: replace_coeff_add roth_cast_smult roth_smult_add
      comp mult.commute)
  show ?thesis
    using d e eq
    by (intro exI[of _ "d*e"] exI[of _ "smult e Q + smult d S"]) auto
qed

lemma roth_clear_polynomial:
  fixes P :: "rat mpoly"
  shows "\<exists>d::int. d>0 \<and> (\<exists>Q::int mpoly.
    replace_coeff of_int Q = smult (of_int d) P)"
proof (induction P rule: mpoly_induct)
  case (monom m a)
  show ?case by (rule roth_clear_monom)
next
  case (sum p1 p2 m a)
  show ?case by (rule roth_clear_add) (use sum.IH in auto)
qed

lemma roth_integral_rep_exists:
  "\<exists>Q. roth_integral_rep P Q"
proof -
  obtain d::int and Q::"int mpoly" where d: "d>0"
    and eq: "replace_coeff of_int Q = smult (of_int d) P"
    using roth_clear_polynomial[of P] by blast
  show ?thesis
    unfolding roth_integral_rep_def using d eq
    by (intro exI[of _ Q] exI[of _ "of_int d"]) auto
qed

definition roth_proj_height :: "rat mpoly \<Rightarrow> nat" where
  "roth_proj_height P =
    Inf {roth_int_coeff_sup Q | Q. roth_integral_rep P Q}"

definition roth_proj_log_height :: "rat mpoly \<Rightarrow> real" where
  "roth_proj_log_height P = ln (real (roth_proj_height P))"

lemma roth_proj_height_ge_one [simp]:
  "1 \<le> roth_proj_height P"
proof -
  have ne: "{roth_int_coeff_sup Q | Q. roth_integral_rep P Q} \<noteq> {}"
    using roth_integral_rep_exists[of P] by auto
  have lower: "\<And>x. x \<in> {roth_int_coeff_sup Q | Q.
    roth_integral_rep P Q} \<Longrightarrow> 1 \<le> x"
    by (auto simp: roth_int_coeff_sup_def intro!: Max_ge)
  show ?thesis
    unfolding roth_proj_height_def
    by (rule cInf_greatest[OF ne lower])
qed

lemma roth_proj_log_height_nonneg [simp]:
  "0 \<le> roth_proj_log_height P"
  using roth_proj_height_ge_one[of P]
  by (simp add: roth_proj_log_height_def)

lemma roth_proj_height_attained:
  "\<exists>Q. roth_integral_rep P Q \<and>
    roth_int_coeff_sup Q = roth_proj_height P"
  unfolding roth_proj_height_def
  using Inf_nat_def1[of "{roth_int_coeff_sup Q | Q.
    roth_integral_rep P Q}"] roth_integral_rep_exists[of P]
  by auto

lemma roth_proj_height_le:
  assumes "roth_integral_rep P Q"
  shows "roth_proj_height P \<le> roth_int_coeff_sup Q"
  unfolding roth_proj_height_def
  by (rule cInf_lower) (use assms in auto)

lemma roth_proj_height_cast:
  "roth_proj_height (replace_coeff of_int Q) \<le>
    roth_int_coeff_sup Q"
  by (rule roth_proj_height_le[OF roth_integral_rep_cast])

lemma roth_proj_height_smult:
  assumes "a \<noteq> (0::rat)"
  shows "roth_proj_height (smult a P) = roth_proj_height P"
  by (simp add: roth_proj_height_def roth_integral_rep_smult[OF assms])

lemma roth_proj_log_height_smult:
  assumes "a \<noteq> (0::rat)"
  shows "roth_proj_log_height (smult a P) =
    roth_proj_log_height P"
  by (simp add: roth_proj_log_height_def roth_proj_height_smult[OF assms])

section \<open>Coefficient content of disjoint products\<close>

lemma roth_coeffs_eq:
  "coeffs P = {coeff P I | I.
    I \<in> Poly_Mapping.keys (mapping_of P)}"
  by (auto simp: coeffs.rep_eq coeff_def
    Poly_Mapping.range.rep_eq in_keys_iff)

lemma roth_coeffs_nonempty:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0"
  shows "coeffs P \<noteq> {}"
proof
  assume empty: "coeffs P = {}"
  have ki: "I \<notin> Poly_Mapping.keys (mapping_of P)" for I
    using empty by (auto simp: roth_coeffs_eq)
  have keys: "Poly_Mapping.keys (mapping_of P) = {}"
    by (rule set_eqI) (simp add: ki)
  have eq: "mapping_of P = 0" using keys by simp
  have eq0: "mapping_of P = mapping_of (0::int mpoly)"
    using eq by (simp add: zero_mpoly.rep_eq)
  show False using eq0 p by (simp add: mapping_of_inject)
qed

lemma roth_int_coeff_sup_eq_Max:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0"
  shows "roth_int_coeff_sup P =
    Max ((\<lambda>c. nat (abs c)) ` coeffs P)"
proof -
  obtain c where c: "c \<in> coeffs P"
    using roth_coeffs_nonempty[OF p] by blast
  have cnz: "c \<noteq> 0"
    using c by (auto simp: coeffs.rep_eq Poly_Mapping.range.rep_eq)
  have cge: "1 \<le> nat (abs c)" using cnz by simp
  have m: "nat (abs c) \<le>
    Max ((\<lambda>c. nat (abs c)) ` coeffs P)"
    by (rule Max_ge) (use c in auto)
  have le: "1 \<le>
    Max ((\<lambda>c. nat (abs c)) ` coeffs P)"
    using cge m by linarith
  have ne: "((\<lambda>c. nat (abs c)) ` coeffs P) \<noteq> {}"
    using roth_coeffs_nonempty[OF p] by auto
  show ?thesis using le ne
    by (simp add: roth_int_coeff_sup_def Max_insert)
qed

lemma roth_Max_products:
  fixes A B :: "nat set"
  assumes fa: "finite A" and fb: "finite B"
    and na: "A \<noteq> {}" and nb: "B \<noteq> {}"
  shows "Max {a*b | a b. a \<in> A \<and> b \<in> B} = Max A * Max B"
proof (rule Max_eqI)
  have eq: "{a*b | a b. a \<in> A \<and> b \<in> B} =
    (\<lambda>(a,b). a*b) ` (A \<times> B)" by auto
  show "finite {a*b | a b. a \<in> A \<and> b \<in> B}"
    using fa fb by (simp add: eq)
  show "y \<le> Max A * Max B"
    if "y \<in> {a*b | a b. a \<in> A \<and> b \<in> B}" for y
    using that fa fb by (auto intro: mult_le_mono Max_ge)
  show "Max A * Max B \<in>
    {a*b | a b. a \<in> A \<and> b \<in> B}"
    using Max_in[OF fa na] Max_in[OF fb nb] by blast
qed

lemma roth_coeffs_disjoint_mult:
  fixes P Q :: "int mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
  shows "coeffs (P*Q) =
    {a*b | a b. a \<in> coeffs P \<and> b \<in> coeffs Q}"
proof (rule equalityI)
  show "coeffs (P*Q) \<subseteq>
    {a*b | a b. a \<in> coeffs P \<and> b \<in> coeffs Q}"
  proof (rule subsetI)
    fix c assume c: "c \<in> coeffs (P*Q)"
    then obtain K where
      K: "K \<in> Poly_Mapping.keys (mapping_of (P*Q))"
      and cK: "c = coeff (P*Q) K"
      by (auto simp: roth_coeffs_eq)
    obtain I J where
      i: "I \<in> Poly_Mapping.keys (mapping_of P)"
      and j: "J \<in> Poly_Mapping.keys (mapping_of Q)"
      and k: "K = I+J"
      using K Poly_Mapping.keys_mult
        [of "mapping_of P" "mapping_of Q"]
      by (auto simp: times_mpoly.rep_eq)
    have cpq: "coeff (P*Q) K = coeff P I * coeff Q J"
      using k roth_disjoint_prod_coeff[OF disj i j] by simp
    show "c \<in> {a*b | a b.
      a \<in> coeffs P \<and> b \<in> coeffs Q}"
      using cK cpq i j by (auto simp: roth_coeffs_eq)
  qed
  show "{a*b | a b. a \<in> coeffs P \<and> b \<in> coeffs Q}
    \<subseteq> coeffs (P*Q)"
  proof (rule subsetI)
    fix c assume "c \<in> {a*b | a b.
      a \<in> coeffs P \<and> b \<in> coeffs Q}"
    then obtain a b where
      a: "a \<in> coeffs P"
      and b: "b \<in> coeffs Q"
      and c: "c = a*b" by blast
    obtain I where
      i: "I \<in> Poly_Mapping.keys (mapping_of P)"
      and ai: "a = coeff P I"
      using a by (auto simp: roth_coeffs_eq)
    obtain J where
      j: "J \<in> Poly_Mapping.keys (mapping_of Q)"
      and bj: "b = coeff Q J"
      using b by (auto simp: roth_coeffs_eq)
    have nz: "coeff (P*Q) (I+J) \<noteq> 0"
      using roth_disjoint_prod_coeff[OF disj i j] i j
      by (simp add: coeff_def in_keys_iff)
    have k: "I+J \<in> Poly_Mapping.keys (mapping_of (P*Q))"
      using nz by (simp add: coeff_def in_keys_iff)
    have cpq: "coeff (P*Q) (I+J) = c"
      using c ai bj roth_disjoint_prod_coeff[OF disj i j]
      by simp
    show "c \<in> coeffs (P*Q)"
      using k cpq by (auto simp: roth_coeffs_eq)
  qed
qed

lemma roth_Gcd_products:
  fixes A B :: "int set"
  shows "Gcd {a*b | a b. a \<in> A \<and> b \<in> B} = Gcd A * Gcd B"
proof (rule associated_eqI)
  let ?S = "{a*b | a b. a \<in> A \<and> b \<in> B}"
  have Sb: "Gcd ?S dvd a * Gcd B" if "a \<in> A" for a
  proof -
    have h: "Gcd ?S dvd Gcd ((*) a ` B)"
      using that by (auto intro: Gcd_greatest Gcd_dvd)
    show ?thesis using h by (simp add: Gcd_mult dvd_normalize_iff)
  qed
  have h2: "Gcd ?S dvd Gcd ((\<lambda>a. a * Gcd B) ` A)"
    by (rule Gcd_greatest) (auto intro: Sb)
  have eq: "((\<lambda>a. a * Gcd B) ` A) = ((*) (Gcd B) ` A)"
    by auto
  have h3: "Gcd ((\<lambda>a. a * Gcd B) ` A) = Gcd B * Gcd A"
    using eq by (simp add: Gcd_mult normalize_mult)
  have h4: "Gcd ?S dvd Gcd B * Gcd A"
    using h2 h3 by simp
  show "Gcd ?S dvd Gcd A * Gcd B"
    using h4 by (simp only: mult.commute[of "Gcd A" "Gcd B"])
  show "Gcd A * Gcd B dvd Gcd ?S"
    by (rule Gcd_greatest) (auto intro: mult_dvd_mono Gcd_dvd)
  show "normalize (Gcd ?S) = Gcd ?S" by simp
  show "normalize (Gcd A * Gcd B) = Gcd A * Gcd B"
    by (simp add: normalize_mult)
qed

lemma roth_content_disjoint_mult:
  fixes P Q :: "int mpoly"
  assumes "vars P \<inter> vars Q = {}"
  shows "Gcd (coeffs (P*Q)) = Gcd (coeffs P) * Gcd (coeffs Q)"
  by (simp add: roth_coeffs_disjoint_mult[OF assms] roth_Gcd_products)

lemma roth_primitive_disjoint_mult:
  fixes P Q :: "int mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
    and p: "primitive P" and q: "primitive Q"
  shows "primitive (P*Q)"
  using assms
  by (simp add: primitive_def roth_content_disjoint_mult)

lemma roth_int_coeff_sup_disjoint_mult:
  fixes P Q :: "int mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
    and p: "P \<noteq> 0" and q: "Q \<noteq> 0"
  shows "roth_int_coeff_sup (P*Q) =
    roth_int_coeff_sup P * roth_int_coeff_sup Q"
proof -
  let ?A = "(\<lambda>c. nat (abs c)) ` coeffs P"
  let ?B = "(\<lambda>c. nat (abs c)) ` coeffs Q"
  have eq: "(\<lambda>c. nat (abs c)) ` coeffs (P*Q) =
    {a*b | a b. a \<in> ?A \<and> b \<in> ?B}"
  proof (rule equalityI)
    show "(\<lambda>c. nat (abs c)) ` coeffs (P*Q) \<subseteq>
      {a*b | a b. a \<in> ?A \<and> b \<in> ?B}"
    proof
      fix x assume "x \<in>
        (\<lambda>c. nat (abs c)) ` coeffs (P*Q)"
      then obtain c where c: "c \<in> coeffs (P*Q)"
        and x: "x = nat (abs c)" by blast
      obtain a b where a: "a \<in> coeffs P"
        and b: "b \<in> coeffs Q" and c: "c = a*b"
        using c roth_coeffs_disjoint_mult[OF disj] by blast
      have aa: "nat (abs a) \<in> ?A" using a by blast
      have bb: "nat (abs b) \<in> ?B" using b by blast
      have xeq: "x = nat (abs a) * nat (abs b)"
        using x c by (simp add: nat_abs_mult_distrib)
      show "x \<in> {a*b | a b. a \<in> ?A \<and> b \<in> ?B}"
        using aa bb xeq by blast
    qed
    show "{a*b | a b. a \<in> ?A \<and> b \<in> ?B} \<subseteq>
      (\<lambda>c. nat (abs c)) ` coeffs (P*Q)"
    proof
      fix x assume "x \<in>
        {a*b | a b. a \<in> ?A \<and> b \<in> ?B}"
      then obtain a b where a: "a \<in> ?A"
        and b: "b \<in> ?B" and x: "x = a*b" by blast
      obtain c where c: "c \<in> coeffs P"
        and a: "a = nat (abs c)" using a by blast
      obtain d where d: "d \<in> coeffs Q"
        and b: "b = nat (abs d)" using b by blast
      have cd: "c*d \<in> coeffs (P*Q)"
        using c d roth_coeffs_disjoint_mult[OF disj] by blast
      have xeq: "x = nat (abs (c*d))"
        using x a b by (simp add: nat_abs_mult_distrib)
      show "x \<in> (\<lambda>c. nat (abs c)) ` coeffs (P*Q)"
        using cd xeq by blast
    qed
  qed
  have finA: "finite ?A" and finB: "finite ?B" by auto
  have neA: "?A \<noteq> {}" and neB: "?B \<noteq> {}"
    using roth_coeffs_nonempty[OF p]
      roth_coeffs_nonempty[OF q] by auto
  have pq: "P*Q \<noteq> 0" using p q by auto
  show ?thesis
    using roth_Max_products[OF finA finB neA neB] eq
    by (simp add: roth_int_coeff_sup_eq_Max[OF pq]
      roth_int_coeff_sup_eq_Max[OF p]
      roth_int_coeff_sup_eq_Max[OF q])
qed

section \<open>Primitive integral representatives\<close>

lemma roth_coeff_sdiv:
  fixes P :: "int mpoly"
  shows "coeff (sdiv d P) I = coeff P I div d"
  by (simp add: coeff_def sdiv.rep_eq
    Poly_Mapping.map.rep_eq when_def)

lemma roth_coeff_smult:
  fixes P :: "int mpoly"
  shows "coeff (smult d P) I = d * coeff P I"
  by (simp add: coeff_def smult.rep_eq
    Poly_Mapping.map.rep_eq when_def)

lemma roth_coeff_zero:
  "coeff (0::int mpoly) I = 0"
  by (simp add: coeff_def zero_mpoly.rep_eq)

lemma roth_smult_nonzero:
  fixes P :: "int mpoly"
  assumes d: "d \<noteq> 0" and p: "P \<noteq> 0"
  shows "smult d P \<noteq> 0"
proof
  assume z: "smult d P = 0"
  have ci: "coeff P I = 0" for I
    using arg_cong[OF z, of "\<lambda>P. coeff P I"]
      roth_coeff_zero[of I] d
    by (simp add: roth_coeff_smult)
  have zp: "P = 0" using ci roth_coeff_zero
    by (simp add: coeff_eq[symmetric] fun_eq_iff)
  show False using p zp by simp
qed

lemma roth_content_dvd_coeff:
  fixes P :: "int mpoly"
  shows "Gcd (coeffs P) dvd coeff P I"
  by (cases "coeff P I = 0")
    (auto simp: roth_coeffs_eq coeff_def in_keys_iff
      intro: Gcd_dvd)

lemma roth_content_sdiv:
  fixes P :: "int mpoly"
  shows "smult (Gcd (coeffs P))
    (sdiv (Gcd (coeffs P)) P) = P"
  by (simp add: coeff_eq[symmetric] fun_eq_iff
    roth_coeff_smult roth_coeff_sdiv roth_content_dvd_coeff)

lemma roth_keys_smult:
  fixes P :: "int mpoly"
  assumes d: "d \<noteq> 0"
  shows "Poly_Mapping.keys (mapping_of (smult d P)) =
    Poly_Mapping.keys (mapping_of P)"
  using d by (auto simp: in_keys_iff coeff_def[symmetric]
    roth_coeff_smult)

lemma roth_coeffs_smult:
  fixes P :: "int mpoly"
  assumes d: "d \<noteq> 0"
  shows "coeffs (smult d P) = ((*) d) ` coeffs P"
  by (auto simp: roth_coeffs_eq roth_coeff_smult
    roth_keys_smult[OF d])

lemma roth_content_pos:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0"
  shows "0 < Gcd (coeffs P)"
proof -
  obtain c where c: "c \<in> coeffs P"
    using roth_coeffs_nonempty[OF p] by blast
  have cnz: "c \<noteq> 0" using c
    by (auto simp: coeffs.rep_eq Poly_Mapping.range.rep_eq)
  have g: "Gcd (coeffs P) \<noteq> 0"
    using Gcd_dvd[OF c] cnz by auto
  have nonneg: "0 \<le> Gcd (coeffs P)"
    using normalize_Gcd[of "coeffs P"]
    by (metis abs_ge_zero normalize_int_def)
  show ?thesis using g nonneg by linarith
qed

lemma roth_sdiv_primitive:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0"
  shows "primitive (sdiv (Gcd (coeffs P)) P)"
proof -
  let ?d = "Gcd (coeffs P)"
  have d: "0 < ?d" by (rule roth_content_pos[OF p])
  have eq: "P = smult ?d (sdiv ?d P)"
    using roth_content_sdiv by simp
  have h: "Gcd (coeffs P) =
    Gcd (coeffs (smult ?d (sdiv ?d P)))"
    using eq by simp
  have h2: "Gcd (coeffs (smult ?d (sdiv ?d P))) =
    normalize (?d * Gcd (coeffs (sdiv ?d P)))"
    using d by (simp only: roth_coeffs_smult Gcd_mult)
  have gcd1: "?d = normalize
    (?d * Gcd (coeffs (sdiv ?d P)))"
    using h h2 by simp
  have nonneg: "0 \<le> Gcd (coeffs (sdiv ?d P))"
    using normalize_Gcd[of "coeffs (sdiv ?d P)"]
    by (metis abs_ge_zero normalize_int_def)
  have gcd: "?d = ?d * Gcd (coeffs (sdiv ?d P))"
    using gcd1 d nonneg by (simp add: normalize_int_def)
  have "?d * 1 = ?d * Gcd (coeffs (sdiv ?d P))"
    using gcd by simp
  then have g1: "Gcd (coeffs (sdiv ?d P)) = 1"
    using d by (simp only: mult_left_cancel)
  show ?thesis using g1 by (simp add: primitive_def)
qed

lemma roth_Max_scale:
  fixes A :: "nat set"
  assumes fin: "finite A" and ne: "A \<noteq> {}"
  shows "Max ((*) d ` A) = d * Max A"
proof (rule Max_eqI)
  show "finite ((*) d ` A)" using fin by simp
  show "y \<le> d * Max A" if "y \<in> (*) d ` A" for y
    using that fin by (auto intro: mult_le_mono1 Max_ge)
  show "d * Max A \<in> (*) d ` A"
    using Max_in[OF fin ne] by blast
qed

lemma roth_int_coeff_sup_smult:
  fixes P :: "int mpoly"
  assumes d: "d \<noteq> 0" and p: "P \<noteq> 0"
  shows "roth_int_coeff_sup (smult d P) =
    nat (abs d) * roth_int_coeff_sup P"
proof -
  have dp: "smult d P \<noteq> 0"
    by (rule roth_smult_nonzero[OF d p])
  let ?A = "(\<lambda>c. nat (abs c)) ` coeffs P"
  have eq: "(\<lambda>c. nat (abs c)) ` coeffs (smult d P) =
    ((*) (nat (abs d))) ` ?A"
    by (simp add: roth_coeffs_smult[OF d] image_image
      nat_abs_mult_distrib)
  have fin: "finite ?A" by simp
  have ne: "?A \<noteq> {}"
    using roth_coeffs_nonempty[OF p] by simp
  show ?thesis
    using eq roth_Max_scale[OF fin ne, of "nat (abs d)"]
    by (simp add: roth_int_coeff_sup_eq_Max[OF dp]
      roth_int_coeff_sup_eq_Max[OF p])
qed

lemma roth_coeff_smult_rat:
  fixes P :: "rat mpoly"
  shows "coeff (smult d P) I = d * coeff P I"
  by (simp add: coeff_def smult.rep_eq
    Poly_Mapping.map.rep_eq when_def)

lemma roth_coeff_cast:
  fixes P :: "int mpoly"
  shows "coeff (replace_coeff of_int P) I =
    of_int (coeff P I)"
  by (simp add: coeff_replace_coeff)

lemma roth_primitive_scalar_integral:
  fixes P Q :: "int mpoly" and c :: rat
  assumes prim: "primitive P"
    and eq: "replace_coeff of_int Q =
      smult c (replace_coeff of_int P)"
  shows "\<exists>z::int. c = of_int z"
proof -
  obtain a b :: int where quot: "quotient_of c = (a,b)"
    by (cases "quotient_of c") auto
  have bp: "b > 0" by (rule quotient_of_denom_pos[OF quot])
  have cop: "coprime a b"
    by (rule quotient_of_coprime[OF quot])
  have ceq: "c = of_int a / of_int b"
    by (rule quotient_of_div[OF quot])
  have coef: "of_int (coeff Q I) =
    c * of_int (coeff P I)" for I
    using arg_cong[OF eq, of "\<lambda>P. coeff P I"]
    by (simp add: roth_coeff_cast roth_coeff_smult_rat)
  have rat: "(of_int (b * coeff Q I)::rat) =
    of_int (a * coeff P I)" for I
    using coef[of I] ceq bp by (simp add: field_simps)
  have dvd: "b dvd coeff P I" for I
  proof -
    have ieq: "b * coeff Q I = a * coeff P I"
      using rat[of I] by (metis of_int_eq_iff)
    have bd: "b dvd a * coeff P I"
      using ieq by (metis dvd_triv_left)
    show ?thesis using bd cop
      by (simp add: coprime_commute
        coprime_dvd_mult_right_iff)
  qed
  have gcd: "b dvd Gcd (coeffs P)"
    by (rule Gcd_greatest)
      (auto simp: roth_coeffs_eq intro: dvd)
  have b1: "b = 1" using gcd prim bp
    by (simp add: primitive_def)
  show ?thesis using ceq b1 by auto
qed

lemma roth_cast_smult_inject:
  fixes P Q :: "int mpoly"
  assumes eq: "replace_coeff of_int Q =
    smult (of_int z::rat) (replace_coeff of_int P)"
  shows "Q = smult z P"
  using arg_cong[OF eq, of "\<lambda>P. coeff P"]
  by (auto simp: coeff_eq[symmetric] fun_eq_iff
    roth_coeff_cast roth_coeff_smult roth_coeff_smult_rat;
    metis of_int_eq_iff of_int_mult)

lemma roth_proj_height_cast_primitive:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0" and prim: "primitive P"
  shows "roth_proj_height (replace_coeff of_int P) =
    roth_int_coeff_sup P"
proof (rule antisym)
  show "roth_proj_height (replace_coeff of_int P) \<le>
    roth_int_coeff_sup P"
    by (rule roth_proj_height_cast)
  show "roth_int_coeff_sup P \<le>
    roth_proj_height (replace_coeff of_int P)"
  proof -
    obtain Q where rep:
      "roth_integral_rep (replace_coeff of_int P) Q"
      and min: "roth_int_coeff_sup Q =
        roth_proj_height (replace_coeff of_int P)"
      using roth_proj_height_attained by blast
    obtain c::rat where cnz: "c \<noteq> 0"
      and eq: "replace_coeff of_int Q =
        smult c (replace_coeff of_int P)"
      using rep by (auto simp: roth_integral_rep_def)
    obtain z::int where cz: "c = of_int z"
      using roth_primitive_scalar_integral[OF prim eq] by blast
    have z: "z \<noteq> 0" using cnz cz by auto
    have qeq: "Q = smult z P"
      using roth_cast_smult_inject[of Q z P] eq cz by simp
    have one: "1 \<le> nat (abs z)" using z by simp
    have le: "roth_int_coeff_sup P \<le>
      nat (abs z) * roth_int_coeff_sup P"
      using one by simp
    have finaleq: "roth_proj_height
      (replace_coeff of_int P) =
      nat (abs z) * roth_int_coeff_sup P"
      using min qeq roth_int_coeff_sup_smult[OF z p] by simp
    show ?thesis using le by (simp only: finaleq)
  qed
qed

lemma roth_vars_smult_rat:
  fixes P :: "rat mpoly"
  assumes c: "c \<noteq> 0"
  shows "vars (smult c P) = vars P"
  using c by (auto simp: vars_def coeff_keys roth_coeff_smult_rat)

lemma roth_vars_cast:
  fixes P :: "int mpoly"
  shows "vars (replace_coeff of_int P :: rat mpoly) = vars P"
  by (auto simp: vars_def coeff_keys roth_coeff_cast)

lemma roth_cast_nonzero:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0"
  shows "(replace_coeff of_int P :: rat mpoly) \<noteq> 0"
proof
  assume z: "(replace_coeff of_int P :: rat mpoly) = 0"
  have eq: "(replace_coeff of_int P :: rat mpoly) =
    smult (of_int (0::int))
      (replace_coeff of_int (0::int mpoly))"
    using z by simp
  have "P = 0" using roth_cast_smult_inject[OF eq] by simp
  then show False using p by simp
qed

lemma roth_smult_nonzero_rat:
  fixes P :: "rat mpoly"
  assumes c: "c \<noteq> 0" and p: "P \<noteq> 0"
  shows "smult c P \<noteq> 0"
proof -
  have mz: "coeff (monom 0 c) 0 = c"
    by (simp add: coeff_monom)
  have zz: "coeff (0::rat mpoly) 0 = 0"
    by (simp add: coeff_def zero_mpoly.rep_eq)
  have "monom 0 c \<noteq> (0::rat mpoly)"
    using mz zz c by auto
  then show ?thesis using p
    by (simp add: smult_conv_mult)
qed

lemma roth_integral_rep_sdiv:
  fixes P :: "rat mpoly" and Q :: "int mpoly"
  assumes rep: "roth_integral_rep P Q" and q: "Q \<noteq> 0"
  shows "roth_integral_rep P (sdiv (Gcd (coeffs Q)) Q)"
proof -
  let ?d = "Gcd (coeffs Q)"
  let ?V = "sdiv ?d Q"
  obtain c::rat where c: "c \<noteq> 0"
    and eq: "replace_coeff of_int Q = smult c P"
    using rep by (auto simp: roth_integral_rep_def)
  have d: "?d \<noteq> 0"
    using roth_content_pos[OF q] by linarith
  have h: "(replace_coeff of_int (smult ?d ?V) :: rat mpoly) =
    replace_coeff of_int Q"
    using roth_content_sdiv[of Q] by (rule arg_cong)
  have h2: "(replace_coeff of_int (smult ?d ?V) :: rat mpoly) =
    smult (of_int ?d) (replace_coeff of_int ?V)"
    by (rule roth_cast_smult)
  have eq2: "(replace_coeff of_int Q :: rat mpoly) =
    smult (of_int ?d) (replace_coeff of_int ?V)"
    using h h2 by simp
  have smult1: "smult (1::rat) X = X"
    for X :: "rat mpoly"
    by (simp add: smult_conv_mult)
  have scaled: "smult (inverse (of_int ?d))
    (replace_coeff of_int Q :: rat mpoly) =
    replace_coeff of_int ?V"
    using arg_cong[OF eq2,
        of "smult (inverse (of_int ?d))"] d
    by (simp add: roth_smult_smult smult1)
  have eq3: "(replace_coeff of_int ?V :: rat mpoly) =
    smult (c / of_int ?d) P"
    using scaled eq
    by (simp add: roth_smult_smult divide_inverse mult.commute)
  have cd: "c / of_int ?d \<noteq> 0" using c d by simp
  show ?thesis unfolding roth_integral_rep_def
    using cd eq3 by blast
qed

lemma roth_primitive_rep_exists:
  fixes P :: "rat mpoly"
  assumes p: "P \<noteq> 0"
  shows "\<exists>Q::int mpoly.
    roth_integral_rep P Q \<and> Q \<noteq> 0 \<and> primitive Q"
proof -
  obtain Q::"int mpoly" where rep: "roth_integral_rep P Q"
    using roth_integral_rep_exists[of P] by blast
  obtain c::rat where c: "c \<noteq> 0"
    and eq: "replace_coeff of_int Q = smult c P"
    using rep by (auto simp: roth_integral_rep_def)
  have cast0:
    "(replace_coeff of_int (0::int mpoly) :: rat mpoly) = 0"
    using replace_coeff_monom[of of_int 0 0] by simp
  have q: "Q \<noteq> 0"
    using eq roth_smult_nonzero_rat[OF c p] cast0 by auto
  let ?V = "sdiv (Gcd (coeffs Q)) Q"
  have vrep: "roth_integral_rep P ?V"
    by (rule roth_integral_rep_sdiv[OF rep q])
  have vprim: "primitive ?V"
    by (rule roth_sdiv_primitive[OF q])
  have v: "?V \<noteq> 0"
    using q roth_content_sdiv[of Q]
    by (auto simp: smult_conv_mult)
  show ?thesis using vrep vprim v by blast
qed

lemma roth_proj_height_primitive_rep:
  fixes P :: "rat mpoly" and Q :: "int mpoly"
  assumes p: "P \<noteq> 0" and q: "Q \<noteq> 0"
    and prim: "primitive Q" and rep: "roth_integral_rep P Q"
  shows "roth_proj_height P = roth_int_coeff_sup Q"
proof -
  obtain c::rat where c: "c \<noteq> 0"
    and eq: "replace_coeff of_int Q = smult c P"
    using rep by (auto simp: roth_integral_rep_def)
  have h: "roth_proj_height (replace_coeff of_int Q) =
    roth_proj_height P"
    using eq roth_proj_height_smult[OF c, of P] by simp
  show ?thesis
    using h roth_proj_height_cast_primitive[OF q prim] by simp
qed

lemma roth_cast_mult:
  fixes P Q :: "int mpoly"
  shows "(replace_coeff of_int (P*Q) :: rat mpoly) =
    replace_coeff of_int P * replace_coeff of_int Q"
  by (rule roth_replace_coeff_mult) simp_all

lemma roth_integral_rep_mult:
  fixes P Q :: "rat mpoly" and U V :: "int mpoly"
  assumes u: "roth_integral_rep P U"
    and v: "roth_integral_rep Q V"
  shows "roth_integral_rep (P*Q) (U*V)"
proof -
  obtain c::rat where c: "c \<noteq> 0"
    and ceq: "replace_coeff of_int U = smult c P"
    using u by (auto simp: roth_integral_rep_def)
  obtain d::rat where d: "d \<noteq> 0"
    and deq: "replace_coeff of_int V = smult d Q"
    using v by (auto simp: roth_integral_rep_def)
  have eq: "(replace_coeff of_int (U*V) :: rat mpoly) =
    smult (c*d) (P*Q)"
    using ceq deq
    by (simp add: roth_cast_mult mult_smult_left
      smult_conv_mult mult_monom algebra_simps)
  have cd: "c*d \<noteq> 0" using c d by simp
  show ?thesis unfolding roth_integral_rep_def
    using cd eq by blast
qed

lemma roth_vars_integral_rep:
  fixes P :: "rat mpoly" and U :: "int mpoly"
  assumes u: "roth_integral_rep P U"
  shows "vars U = vars P"
proof -
  obtain c::rat where c: "c \<noteq> 0"
    and eq: "replace_coeff of_int U = smult c P"
    using u by (auto simp: roth_integral_rep_def)
  show ?thesis
    using arg_cong[OF eq, of vars] roth_vars_cast[of U]
      roth_vars_smult_rat[OF c, of P]
    by simp
qed

lemma roth_proj_height_disjoint_mult:
  fixes P Q :: "rat mpoly"
  assumes p: "P \<noteq> 0" and q: "Q \<noteq> 0"
    and disj: "vars P \<inter> vars Q = {}"
  shows "roth_proj_height (P*Q) =
    roth_proj_height P * roth_proj_height Q"
proof -
  obtain U::"int mpoly" where
    urep: "roth_integral_rep P U" and u: "U \<noteq> 0"
    and uprim: "primitive U"
    using roth_primitive_rep_exists[OF p] by blast
  obtain V::"int mpoly" where
    vrep: "roth_integral_rep Q V" and v: "V \<noteq> 0"
    and vprim: "primitive V"
    using roth_primitive_rep_exists[OF q] by blast
  have duv: "vars U \<inter> vars V = {}"
    using disj roth_vars_integral_rep[OF urep]
      roth_vars_integral_rep[OF vrep] by simp
  have uvprim: "primitive (U*V)"
    by (rule roth_primitive_disjoint_mult[OF duv uprim vprim])
  have uvrep: "roth_integral_rep (P*Q) (U*V)"
    by (rule roth_integral_rep_mult[OF urep vrep])
  have puv: "P*Q \<noteq> 0" using p q by simp
  have uuv: "U*V \<noteq> 0" using u v by simp
  have h1: "roth_proj_height (P*Q) =
    roth_int_coeff_sup (U*V)"
    by (rule roth_proj_height_primitive_rep[OF
      puv uuv uvprim uvrep])
  have h2: "roth_proj_height P = roth_int_coeff_sup U"
    by (rule roth_proj_height_primitive_rep[OF p u uprim urep])
  have h3: "roth_proj_height Q = roth_int_coeff_sup V"
    by (rule roth_proj_height_primitive_rep[OF q v vprim vrep])
  show ?thesis
    using h1 h2 h3 roth_int_coeff_sup_disjoint_mult[OF duv u v]
    by simp
qed

lemma roth_proj_log_height_disjoint_mult:
  fixes P Q :: "rat mpoly"
  assumes p: "P \<noteq> 0" and q: "Q \<noteq> 0"
    and disj: "vars P \<inter> vars Q = {}"
  shows "roth_proj_log_height (P*Q) =
    roth_proj_log_height P + roth_proj_log_height Q"
  using roth_proj_height_disjoint_mult[OF assms]
    roth_proj_height_ge_one[of P]
    roth_proj_height_ge_one[of Q]
  by (simp add: roth_proj_log_height_def ln_mult)

lemma roth_proj_log_height_disjoint_factor_le:
  fixes P Q :: "rat mpoly"
  assumes p: "P \<noteq> 0" and q: "Q \<noteq> 0"
    and disj: "vars P \<inter> vars Q = {}"
  shows "roth_proj_log_height P \<le>
    roth_proj_log_height (P*Q)"
  using roth_proj_log_height_disjoint_mult[OF assms]
    roth_proj_log_height_nonneg[of Q]
  by simp

end
