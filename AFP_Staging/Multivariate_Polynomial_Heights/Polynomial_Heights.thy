theory Polynomial_Heights
  imports "Multivariate_Hasse_Derivatives.MPoly_Hasse_Support"
begin

section \<open>Heights at rational points\<close>

definition pheight_rat_height :: "rat \<Rightarrow> nat" where
  "pheight_rat_height x \<equiv>
    nat (max (abs (fst (quotient_of x))) (snd (quotient_of x)))"

definition pheight_rat_log_height :: "rat \<Rightarrow> real" where
  "pheight_rat_log_height x \<equiv> ln (real (pheight_rat_height x))"

lemma pheight_rat_height_pos [simp]: "0 < pheight_rat_height x"
  using quotient_of_denom_pos'[of x]
  by (simp add: pheight_rat_height_def)

lemma pheight_rat_height_ge_one [simp]: "1 \<le> pheight_rat_height x"
  using pheight_rat_height_pos[of x] by (simp only: Suc_le_eq)

lemma pheight_rat_log_height_nonneg [simp]: "0 \<le> pheight_rat_log_height x"
  using pheight_rat_height_ge_one[of x]
  by (simp add: pheight_rat_log_height_def)

lemma pheight_rat_height_Fract:
  assumes "q > 0" "coprime p q"
  shows "pheight_rat_height (Fract p q) = nat (max (abs p) q)"
  using assms by (simp add: pheight_rat_height_def quotient_of_Fract)

lemma pheight_rat_log_height_Fract:
  assumes "q > 0" "coprime p q"
  shows "pheight_rat_log_height (Fract p q) = ln (real (nat (max (abs p) q)))"
  using pheight_rat_height_Fract[OF assms]
  by (simp add: pheight_rat_log_height_def)

section \<open>Coefficient sup norm\<close>

definition pheight_int_coeff_sup :: "int mpoly \<Rightarrow> nat" where
  "pheight_int_coeff_sup P \<equiv> Max (insert 1 ((\<lambda>c. nat (abs c)) ` coeffs P))"

lemma pheight_int_coeff_sup_pos [simp]: "0 < pheight_int_coeff_sup P"
proof -
  have h: "1 \<le> Max (insert 1 ((\<lambda>c. nat (abs c)) ` coeffs P))"
    by (rule Max_ge) simp_all
  show ?thesis using h
    unfolding pheight_int_coeff_sup_def by linarith
qed

lemma pheight_int_coeff_sup_ge_one [simp]:
  "1 \<le> pheight_int_coeff_sup P"
  using pheight_int_coeff_sup_pos[of P] by linarith

lemma pheight_int_coeff_sup_coeff:
  "nat (abs (coeff P I)) \<le> pheight_int_coeff_sup P"
proof (cases "coeff P I = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "coeff P I \<in> coeffs P"
    by (simp add: coeff_def in_keys_iff coeffs.rep_eq)
  then have mem: "nat (abs (coeff P I)) \<in> insert 1 ((\<lambda>c. nat (abs c)) ` coeffs P)"
    by blast
  have "nat (abs (coeff P I)) \<le> Max (insert 1 ((\<lambda>c. nat (abs c)) ` coeffs P))"
    by (rule Max_ge) (use mem in simp_all)
  then show ?thesis by (simp add: pheight_int_coeff_sup_def)
qed

section \<open>Projective polynomial height\<close>

definition pheight_integral_rep ::
  "rat mpoly \<Rightarrow> int mpoly \<Rightarrow> bool" where
  "pheight_integral_rep P Q \<equiv>
    (\<exists>c::rat. c \<noteq> 0 \<and> replace_coeff of_int Q = smult c P)"

lemma pheight_smult_smult: "smult a (smult b (P::rat mpoly)) = smult (a*b) P"
  by (simp add: smult_conv_mult mult.assoc mult_monom)

lemma pheight_integral_rep_smult:
  assumes a: "a \<noteq> (0::rat)"
  shows "pheight_integral_rep (smult a P) Q = pheight_integral_rep P Q"
proof (rule iffI)
  assume rep: "pheight_integral_rep (smult a P) Q"
  then obtain c :: rat where c: "c \<noteq> 0"
    and eq: "replace_coeff of_int Q = smult c (smult a P)"
    by (auto simp: pheight_integral_rep_def)
  show "pheight_integral_rep P Q"
    unfolding pheight_integral_rep_def using a c eq
    by (intro exI[of _ "c*a"]) (simp add: pheight_smult_smult)
next
  assume rep: "pheight_integral_rep P Q"
  then obtain c :: rat where c: "c \<noteq> 0" and eq: "replace_coeff of_int Q = smult c P"
    by (auto simp: pheight_integral_rep_def)
  show "pheight_integral_rep (smult a P) Q"
    unfolding pheight_integral_rep_def using a c eq
    by (intro exI[of _ "c/a"]) (simp add: pheight_smult_smult)
qed

lemma pheight_integral_rep_cast: "pheight_integral_rep (replace_coeff of_int Q) Q"
  unfolding pheight_integral_rep_def
  by (rule exI[of _ 1]) (simp add: smult_conv_mult)

section \<open>Clearing denominators\<close>

lemma pheight_rat_clear_denominator:
  obtains d n::int where "d > 0" "(of_int d::rat) * x = of_int n"
proof -
  obtain n d :: int where q: "quotient_of x = (n,d)"
    by (cases "quotient_of x") auto
  have d: "d > 0" using quotient_of_denom_pos[OF q] .
  have x: "x = of_int n / of_int d" using quotient_of_div[OF q] .
  show thesis using that[OF d] x d by simp
qed

lemma pheight_clear_monom:
  fixes x :: rat
  shows "\<exists>d::int. d > 0 \<and> (\<exists>Q::int mpoly. replace_coeff of_int Q = smult (of_int d) (monom I x))"
proof -
  obtain d n::int where d: "d > 0" and dn: "(of_int d::rat) * x = of_int n"
    by (rule pheight_rat_clear_denominator)
  have eq: "replace_coeff of_int (monom I n) = smult (of_int d) (monom I x)"
    using dn by (simp add: replace_coeff_monom)
  show ?thesis using d eq by blast
qed

lemma pheight_smult_add:
  fixes P Q :: "'a::comm_ring_1 mpoly"
  shows "smult a (P+Q) = smult a P + smult a Q"
  by (simp add: smult_conv_mult algebra_simps)

lemma pheight_cast_smult:
  fixes P :: "int mpoly"
  shows "replace_coeff of_int (smult d P) = smult (of_int d::rat) (replace_coeff of_int P)"
  by (induction P rule: mpoly_induct)
     (simp_all add: replace_coeff_monom replace_coeff_add pheight_smult_add)

lemma pheight_clear_add:
  fixes P R :: "rat mpoly"
  assumes P: "\<exists>d::int. d>0 \<and> (\<exists>Q::int mpoly. replace_coeff of_int Q = smult (of_int d) P)"
    and R: "\<exists>e::int. e>0 \<and> (\<exists>S::int mpoly. replace_coeff of_int S = smult (of_int e) R)"
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
  have eq: "replace_coeff of_int (smult e Q + smult d S) = smult (of_int (d*e)) (P+R)"
    using Q S
    by (simp add: replace_coeff_add pheight_cast_smult pheight_smult_add comp mult.commute)
  show ?thesis
    using d e eq
    by (intro exI[of _ "d*e"] exI[of _ "smult e Q + smult d S"]) auto
qed

lemma pheight_clear_polynomial:
  fixes P :: "rat mpoly"
  shows "\<exists>d::int. d>0 \<and> (\<exists>Q::int mpoly.
    replace_coeff of_int Q = smult (of_int d) P)"
proof (induction P rule: mpoly_induct)
  case (monom m a)
  show ?case by (rule pheight_clear_monom)
next
  case (sum p1 p2 m a)
  show ?case by (rule pheight_clear_add) (use sum.IH in auto)
qed

lemma pheight_integral_rep_exists: "\<exists>Q. pheight_integral_rep P Q"
proof -
  obtain d::int and Q::"int mpoly" where d: "d>0"
    and eq: "replace_coeff of_int Q = smult (of_int d) P"
    using pheight_clear_polynomial[of P] by blast
  show ?thesis
    unfolding pheight_integral_rep_def using d eq
    by (intro exI[of _ Q] exI[of _ "of_int d"]) auto
qed

definition pheight_proj_height :: "rat mpoly \<Rightarrow> nat" where
  "pheight_proj_height P \<equiv>
    Inf {pheight_int_coeff_sup Q | Q. pheight_integral_rep P Q}"

definition pheight_proj_log_height :: "rat mpoly \<Rightarrow> real" where
  "pheight_proj_log_height P \<equiv> ln (real (pheight_proj_height P))"

lemma pheight_proj_height_ge_one [simp]:
  "1 \<le> pheight_proj_height P"
proof -
  have ne: "{pheight_int_coeff_sup Q | Q. pheight_integral_rep P Q} \<noteq> {}"
    using pheight_integral_rep_exists[of P] by auto
  have lower: "\<And>x. x \<in> {pheight_int_coeff_sup Q | Q. pheight_integral_rep P Q} \<Longrightarrow> 1 \<le> x"
    by (auto simp: pheight_int_coeff_sup_def intro!: Max_ge)
  show ?thesis
    unfolding pheight_proj_height_def
    by (rule cInf_greatest[OF ne lower])
qed

lemma pheight_proj_log_height_nonneg [simp]: "0 \<le> pheight_proj_log_height P"
  using pheight_proj_height_ge_one[of P]
  by (simp add: pheight_proj_log_height_def)

lemma pheight_proj_height_attained:
  "\<exists>Q. pheight_integral_rep P Q \<and> pheight_int_coeff_sup Q = pheight_proj_height P"
  unfolding pheight_proj_height_def
  using pheight_integral_rep_exists[of P]
        Inf_nat_def1[of "{pheight_int_coeff_sup Q | Q. pheight_integral_rep P Q}"]
  by auto

lemma pheight_proj_height_le:
  assumes "pheight_integral_rep P Q"
  shows "pheight_proj_height P \<le> pheight_int_coeff_sup Q"
  unfolding pheight_proj_height_def
  by (rule cInf_lower) (use assms in auto)

lemma pheight_proj_height_cast:
  "pheight_proj_height (replace_coeff of_int Q) \<le> pheight_int_coeff_sup Q"
  by (rule pheight_proj_height_le[OF pheight_integral_rep_cast])

lemma pheight_proj_height_smult:
  assumes "a \<noteq> 0"
  shows "pheight_proj_height (smult a P) = pheight_proj_height P"
  by (simp add: pheight_proj_height_def pheight_integral_rep_smult[OF assms])

lemma pheight_proj_log_height_smult:
  assumes "a \<noteq> 0"
  shows "pheight_proj_log_height (smult a P) = pheight_proj_log_height P"
  by (simp add: pheight_proj_log_height_def pheight_proj_height_smult[OF assms])

section \<open>Coefficient content of disjoint products\<close>

lemma pheight_coeffs_eq:
  "coeffs P = {coeff P I | I. I \<in> Poly_Mapping.keys (mapping_of P)}"
  by (auto simp: coeffs.rep_eq coeff_def Poly_Mapping.range.rep_eq in_keys_iff)

lemma pheight_coeffs_nonempty:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0"
  shows "coeffs P \<noteq> {}"
proof
  assume empty: "coeffs P = {}"
  have ki: "I \<notin> Poly_Mapping.keys (mapping_of P)" for I
    using empty by (auto simp: pheight_coeffs_eq)
  have "Poly_Mapping.keys (mapping_of P) = {}"
    by (rule set_eqI) (simp add: ki)
  then have "mapping_of P = mapping_of (0::int mpoly)"
    by (simp add: zero_mpoly.rep_eq)
  with p show False by (simp add: mapping_of_inject)
qed

lemma pheight_int_coeff_sup_eq_Max:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0"
  shows "pheight_int_coeff_sup P = Max ((\<lambda>c. nat (abs c)) ` coeffs P)"
proof -
  obtain c where c: "c \<in> coeffs P"
    using pheight_coeffs_nonempty[OF p] by blast
  have cnz: "c \<noteq> 0"
    using c by (auto simp: coeffs.rep_eq Poly_Mapping.range.rep_eq)
  have "1 \<le> nat (abs c)" using cnz by simp
  moreover have "nat (abs c) \<le> Max ((\<lambda>c. nat (abs c)) ` coeffs P)"
    by (rule Max_ge) (use c in auto)
  moreover have "((\<lambda>c. nat (abs c)) ` coeffs P) \<noteq> {}"
    using pheight_coeffs_nonempty[OF p] by auto
  ultimately show ?thesis
    by (simp add: pheight_int_coeff_sup_def)
qed

lemma pheight_Max_products:
  fixes A B :: "nat set"
  assumes fa: "finite A" and fb: "finite B"
    and na: "A \<noteq> {}" and nb: "B \<noteq> {}"
  shows "Max {a*b | a b. a \<in> A \<and> b \<in> B} = Max A * Max B"
proof (rule Max_eqI)
  have eq: "{a*b | a b. a \<in> A \<and> b \<in> B} = (\<lambda>(a,b). a*b) ` (A \<times> B)" by auto
  show "finite {a*b | a b. a \<in> A \<and> b \<in> B}"
    using fa fb by (simp add: eq)
  show "y \<le> Max A * Max B"
    if "y \<in> {a*b | a b. a \<in> A \<and> b \<in> B}" for y
    using that fa fb by (auto intro: mult_le_mono Max_ge)
  show "Max A * Max B \<in> {a*b | a b. a \<in> A \<and> b \<in> B}"
    using Max_in[OF fa na] Max_in[OF fb nb] by blast
qed

lemma pheight_coeffs_disjoint_mult:
  fixes P Q :: "int mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
  shows "coeffs (P*Q) = {a*b | a b. a \<in> coeffs P \<and> b \<in> coeffs Q}"  (is "?L = ?R")
proof (intro equalityI subsetI)
  fix c assume c: "c \<in> ?L"
  then obtain K where K: "K \<in> Poly_Mapping.keys (mapping_of (P*Q))"  "c = coeff (P*Q) K"
    by (auto simp: pheight_coeffs_eq)
  obtain I J where i: "I \<in> Poly_Mapping.keys (mapping_of P)"
        and j: "J \<in> Poly_Mapping.keys (mapping_of Q)"
        and k: "K = I+J"
    using K Poly_Mapping.keys_mult [of "mapping_of P" "mapping_of Q"]
    by (auto simp: times_mpoly.rep_eq)
  have cpq: "coeff (P*Q) K = coeff P I * coeff Q J"
    using k pjet_disjoint_prod_coeff[OF disj i j] by simp
  show "c \<in> ?R"
    using K cpq i j by (auto simp: pheight_coeffs_eq)
next
  fix c assume "c \<in> {a*b | a b. a \<in> coeffs P \<and> b \<in> coeffs Q}"
  then obtain a b where a: "a \<in> coeffs P" and b: "b \<in> coeffs Q" and c: "c = a*b" by blast
  obtain I J where i: "I \<in> Poly_Mapping.keys (mapping_of P)" and ai: "a = coeff P I"
    and j: "J \<in> Poly_Mapping.keys (mapping_of Q)" and bj: "b = coeff Q J"
    using a b by (auto simp: pheight_coeffs_eq)
  have "coeff (P*Q) (I+J) \<noteq> 0"
    using pjet_disjoint_prod_coeff[OF disj] i j
    by (simp add: coeff_def in_keys_iff)
  then have k: "I+J \<in> Poly_Mapping.keys (mapping_of (P*Q))"
    by (simp add: coeff_def in_keys_iff)
  have "coeff (P*Q) (I+J) = c"
    using c ai bj pjet_disjoint_prod_coeff[OF disj] i j by simp
  then show "c \<in> ?L"
    using k by (auto simp: pheight_coeffs_eq)
qed

lemma pheight_Gcd_products:
  fixes A B :: "int set"
  shows "Gcd {a*b | a b. a \<in> A \<and> b \<in> B} = Gcd A * Gcd B"
proof (rule associated_eqI)
  let ?S = "{a*b | a b. a \<in> A \<and> b \<in> B}"
  have Sb: "Gcd ?S dvd a * Gcd B" if "a \<in> A" for a
  proof -
    have "Gcd ?S dvd Gcd ((*) a ` B)"
      using that by (auto intro: Gcd_greatest Gcd_dvd)
    then show ?thesis by (simp add: Gcd_mult)
  qed
  have "Gcd ?S dvd Gcd ((\<lambda>a. a * Gcd B) ` A)"
    by (rule Gcd_greatest) (auto intro: Sb)
  then show "Gcd ?S dvd Gcd A * Gcd B"
   by (metis (lifting) ext Gcd_mult dvd_abs_iff mult_commute_abs normalize_int_def)
  show "Gcd A * Gcd B dvd Gcd ?S"
    by (rule Gcd_greatest) (auto intro: mult_dvd_mono Gcd_dvd)
  show "normalize (Gcd A * Gcd B) = Gcd A * Gcd B"
    by (simp add: normalize_mult)
qed auto

lemma pheight_content_disjoint_mult:
  fixes P Q :: "int mpoly"
  assumes "vars P \<inter> vars Q = {}"
  shows "Gcd (coeffs (P*Q)) = Gcd (coeffs P) * Gcd (coeffs Q)"
  by (simp add: pheight_coeffs_disjoint_mult[OF assms] pheight_Gcd_products)

lemma pheight_primitive_disjoint_mult:
  fixes P Q :: "int mpoly"
  assumes "vars P \<inter> vars Q = {}" and "primitive P" and "primitive Q"
  shows "primitive (P*Q)"
  using assms
  by (simp add: primitive_def pheight_content_disjoint_mult)

lemma pheight_int_coeff_sup_disjoint_mult:
  fixes P Q :: "int mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
    and p: "P \<noteq> 0" and q: "Q \<noteq> 0"
  shows "pheight_int_coeff_sup (P*Q) = pheight_int_coeff_sup P * pheight_int_coeff_sup Q"
proof -
  let ?A = "(\<lambda>c. nat (abs c)) ` coeffs P"
  let ?B = "(\<lambda>c. nat (abs c)) ` coeffs Q"
  have eq: "(\<lambda>c. nat (abs c)) ` coeffs (P*Q) = {a*b | a b. a \<in> ?A \<and> b \<in> ?B}"
    by (force simp: pheight_coeffs_disjoint_mult[OF disj] nat_abs_mult_distrib)
  have finA: "finite ?A" and finB: "finite ?B" by auto
  have neA: "?A \<noteq> {}" and neB: "?B \<noteq> {}"
    using pheight_coeffs_nonempty[OF p] pheight_coeffs_nonempty[OF q] by auto
  have pq: "P*Q \<noteq> 0" using p q by auto
  show ?thesis
    using pheight_Max_products[OF finA finB neA neB] eq
    by (simp add: pheight_int_coeff_sup_eq_Max[OF pq]
      pheight_int_coeff_sup_eq_Max[OF p] pheight_int_coeff_sup_eq_Max[OF q])
qed

section \<open>Primitive integral representatives\<close>

lemma pheight_coeff_sdiv:
  fixes P :: "int mpoly"
  shows "coeff (sdiv d P) I = coeff P I div d"
  by (simp add: coeff_def sdiv.rep_eq Poly_Mapping.map.rep_eq when_def)

lemma pheight_coeff_smult:
  fixes P :: "int mpoly"
  shows "coeff (smult d P) I = d * coeff P I"
  by (simp add: coeff_def smult.rep_eq Poly_Mapping.map.rep_eq when_def)

lemma pheight_coeff_zero:
  "coeff (0::int mpoly) I = 0"
  by (simp add: coeff_def zero_mpoly.rep_eq)

lemma pheight_smult_nonzero:
  fixes P :: "int mpoly"
  assumes d: "d \<noteq> 0" and p: "P \<noteq> 0"
  shows "smult d P \<noteq> 0"
proof
  assume z: "smult d P = 0"
  have "coeff P I = 0" for I
    using arg_cong[OF z, of "\<lambda>P. coeff P I"] pheight_coeff_zero[of I] d
    by (simp add: pheight_coeff_smult)
  then have "P = 0" using pheight_coeff_zero
    by (simp add: coeff_eq[symmetric] fun_eq_iff)
  then show False using p by simp
qed

lemma pheight_content_dvd_coeff:
  fixes P :: "int mpoly"
  shows "Gcd (coeffs P) dvd coeff P I"
  by (cases "coeff P I = 0")
    (auto simp: pheight_coeffs_eq coeff_def in_keys_iff intro: Gcd_dvd)

lemma pheight_content_sdiv:
  fixes P :: "int mpoly"
  shows "smult (Gcd (coeffs P))
    (sdiv (Gcd (coeffs P)) P) = P"
  by (simp add: coeff_eq[symmetric] fun_eq_iff
    pheight_coeff_smult pheight_coeff_sdiv pheight_content_dvd_coeff)

lemma pheight_keys_smult:
  fixes P :: "int mpoly"
  assumes d: "d \<noteq> 0"
  shows "Poly_Mapping.keys (mapping_of (smult d P)) = Poly_Mapping.keys (mapping_of P)"
  using d by (auto simp: in_keys_iff coeff_def[symmetric] pheight_coeff_smult)

lemma pheight_coeffs_smult:
  fixes P :: "int mpoly"
  assumes d: "d \<noteq> 0"
  shows "coeffs (smult d P) = ((*) d) ` coeffs P"
  by (auto simp: pheight_coeffs_eq pheight_coeff_smult pheight_keys_smult[OF d])

lemma pheight_content_pos:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0"
  shows "0 < Gcd (coeffs P)"
proof -
  obtain c where c: "c \<in> coeffs P"
    using pheight_coeffs_nonempty[OF p] by blast
  have cnz: "c \<noteq> 0" using c
    by (auto simp: coeffs.rep_eq Poly_Mapping.range.rep_eq)
  have "Gcd (coeffs P) \<noteq> 0"
    using Gcd_dvd[OF c] cnz by auto
  moreover have "0 \<le> Gcd (coeffs P)"
    using normalize_Gcd[of "coeffs P"]
    by (metis abs_ge_zero normalize_int_def)
  ultimately show ?thesis by linarith
qed

lemma pheight_sdiv_primitive:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0"
  shows "primitive (sdiv (Gcd (coeffs P)) P)"
proof -
  let ?d = "Gcd (coeffs P)"
  have d: "0 < ?d" by (rule pheight_content_pos[OF p])
  have eq: "P = smult ?d (sdiv ?d P)"
    using pheight_content_sdiv by simp
  have h: "Gcd (coeffs P) = Gcd (coeffs (smult ?d (sdiv ?d P)))"
    using eq by simp
  have gcd: "?d = normalize (?d * Gcd (coeffs (sdiv ?d P)))"
    using h d by (simp only: pheight_coeffs_smult Gcd_mult)
  have "?d * 1 = ?d * Gcd (coeffs (sdiv ?d P))"
    using gcd d Gcd_int_greater_eq_0 by simp
  then have g1: "Gcd (coeffs (sdiv ?d P)) = 1"
    using d by (simp only: mult_left_cancel)
  show ?thesis using g1 by (simp add: primitive_def)
qed

lemma pheight_Max_scale:
  fixes A :: "nat set"
  assumes "finite A" "A \<noteq> {}"
  shows "Max ((*) d ` A) = d * Max A"
  using assms by (metis hom_Max_commute nat_mult_max_right)

lemma pheight_int_coeff_sup_smult:
  fixes P :: "int mpoly"
  assumes d: "d \<noteq> 0" and p: "P \<noteq> 0"
  shows "pheight_int_coeff_sup (smult d P) = nat (abs d) * pheight_int_coeff_sup P"
proof -
  have dp: "smult d P \<noteq> 0"
    by (rule pheight_smult_nonzero[OF d p])
  let ?A = "(\<lambda>c. nat (abs c)) ` coeffs P"
  have eq: "(\<lambda>c. nat (abs c)) ` coeffs (smult d P) = ((*) (nat (abs d))) ` ?A"
    by (simp add: pheight_coeffs_smult[OF d] image_image nat_abs_mult_distrib)
  have fin: "finite ?A" by simp
  have ne: "?A \<noteq> {}"
    using pheight_coeffs_nonempty[OF p] by simp
  show ?thesis
    using eq pheight_Max_scale[OF fin ne, of "nat (abs d)"]
    by (simp add: pheight_int_coeff_sup_eq_Max[OF dp] pheight_int_coeff_sup_eq_Max[OF p])
qed

lemma pheight_primitive_scalar_integral:
  fixes P Q :: "int mpoly" and c :: rat
  assumes prim: "primitive P"
    and eq: "replace_coeff of_int Q = smult c (replace_coeff of_int P)"
  shows "\<exists>z::int. c = of_int z"
proof -
  obtain a b :: int where quot: "quotient_of c = (a,b)" and ceq: "c = of_int a / of_int b"
    by (metis prod.collapse quotient_of_div)
  have bp: "b > 0" by (rule quotient_of_denom_pos[OF quot])
  have coef: "of_int (coeff Q I) = c * of_int (coeff P I)" for I
    by (metis coeff_replace_coeff of_int_0 pjet_coeff_smult_rat eq)
  have rat: "(of_int (b * coeff Q I)::rat) =
    of_int (a * coeff P I)" for I
    using coef[of I] ceq bp by (simp add: field_simps)
  have dvd: "b dvd coeff P I" for I
  proof -
    have ieq: "b * coeff Q I = a * coeff P I"
      using rat[of I] by (metis of_int_eq_iff)
    have "b dvd a * coeff P I"
      using ieq by (metis dvd_triv_left)
    then show ?thesis using quotient_of_coprime[OF quot]
      by (simp add: coprime_commute coprime_dvd_mult_right_iff)
  qed
  have gcd: "b dvd Gcd (coeffs P)"
  using dvd by (smt (cvc5, trigger_multi) Gcd_greatest mem_Collect_eq pheight_coeffs_eq)
  have b1: "b = 1" using gcd prim bp
    by (simp add: primitive_def)
  show ?thesis using ceq b1 by auto
qed

lemma pheight_cast_smult_inject:
  fixes P Q :: "int mpoly"
  assumes "replace_coeff of_int Q = smult (of_int z::rat) (replace_coeff of_int P)"
  shows "Q = smult z P"
  by (metis (no_types, lifting) ext assms coeff_eq of_int_eq_iff pheight_cast_smult of_int_0 coeff_replace_coeff)

lemma pheight_proj_height_cast_primitive:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0" and prim: "primitive P"
  shows "pheight_proj_height (replace_coeff of_int P) = pheight_int_coeff_sup P"
proof (intro pheight_proj_height_cast antisym)
  show "pheight_int_coeff_sup P \<le> pheight_proj_height (replace_coeff of_int P)"
  proof -
    obtain Q where rep: "pheight_integral_rep (replace_coeff of_int P) Q"
      and min: "pheight_int_coeff_sup Q = pheight_proj_height (replace_coeff of_int P)"
      using pheight_proj_height_attained by blast
    obtain c::rat where cnz: "c \<noteq> 0"
      and eq: "replace_coeff of_int Q = smult c (replace_coeff of_int P)"
      using rep by (auto simp: pheight_integral_rep_def)
    obtain z::int where cz: "c = of_int z"
      using pheight_primitive_scalar_integral[OF prim eq] by blast
    have qeq: "Q = smult z P"
      using pheight_cast_smult_inject[of Q z P] eq cz by simp
    have one: "1 \<le> nat \<bar>z\<bar>" using cnz cz by simp
    have finaleq: "pheight_proj_height (replace_coeff of_int P) = nat \<bar>z\<bar> * pheight_int_coeff_sup P"
      using cnz cz min p qeq by (metis of_int_0 pheight_int_coeff_sup_smult)
    show ?thesis using one by (simp add: finaleq)
  qed
qed

lemma pheight_vars_smult_rat:
  fixes P :: "rat mpoly"
  assumes c: "c \<noteq> 0"
  shows "vars (smult c P) = vars P"
  using c by (auto simp: vars_def coeff_keys pjet_coeff_smult_rat)

lemma pheight_vars_cast:
  fixes P :: "int mpoly"
  shows "vars (replace_coeff of_int P :: rat mpoly) = vars P"
  by (auto simp: vars_def coeff_keys coeff_replace_coeff)

lemma pheight_cast_nonzero:
  fixes P :: "int mpoly"
  assumes "P \<noteq> 0"
  shows "(replace_coeff of_int P :: rat mpoly) \<noteq> 0"
proof
  assume z: "(replace_coeff of_int P :: rat mpoly) = 0"
  have eq: "(replace_coeff of_int P :: rat mpoly) = smult 0 (replace_coeff of_int 0)"
    using z by simp
  then have "P = 0"
    by (metis pheight_cast_smult_inject mult_eq_0_iff of_int_0 smult_conv_mult)
  then show False using assms by simp
qed

lemma pheight_smult_nonzero_rat:
  fixes P :: "rat mpoly"
  assumes c: "c \<noteq> 0" and p: "P \<noteq> 0"
  shows "smult c P \<noteq> 0"
proof -
  have mz: "coeff (monom 0 c) 0 = c"
    by (simp add: coeff_monom)
  have zz: "coeff 0 0 = 0"
    by (simp add: coeff_def zero_mpoly.rep_eq)
  have "monom 0 c \<noteq> 0"
    using mz zz c by auto
  then show ?thesis using p
    by (simp add: smult_conv_mult)
qed

lemma pheight_integral_rep_sdiv:
  fixes P :: "rat mpoly" and Q :: "int mpoly"
  assumes rep: "pheight_integral_rep P Q" and q: "Q \<noteq> 0"
  shows "pheight_integral_rep P (sdiv (Gcd (coeffs Q)) Q)"
proof -
  let ?d = "Gcd (coeffs Q)"
  let ?V = "sdiv ?d Q"
  obtain c::rat where c: "c \<noteq> 0" and eq: "replace_coeff of_int Q = smult c P"
    using rep by (auto simp: pheight_integral_rep_def)
  have d: "?d \<noteq> 0"
    using pheight_content_pos[OF q] by linarith
  have h: "(replace_coeff of_int (smult ?d ?V) :: rat mpoly) = replace_coeff of_int Q"
    using pheight_content_sdiv[of Q] by (rule arg_cong)
  have h2: "(replace_coeff of_int (smult ?d ?V) :: rat mpoly) =
    smult (of_int ?d) (replace_coeff of_int ?V)"
    by (rule pheight_cast_smult)
  have eq2: "(replace_coeff of_int Q :: rat mpoly) =
    smult (of_int ?d) (replace_coeff of_int ?V)"
    using h h2 by simp
  have smult1: "smult 1 X = X"
    for X :: "rat mpoly"
    by (simp add: smult_conv_mult)
  have scaled: "smult (inverse (of_int ?d)) (replace_coeff of_int Q :: rat mpoly) = replace_coeff of_int ?V"
    using arg_cong[OF eq2, of "smult (inverse (of_int ?d))"] d
    by (simp add: pheight_smult_smult smult1)
  have eq3: "(replace_coeff of_int ?V :: rat mpoly) = smult (c / of_int ?d) P"
    using scaled eq
    by (simp add: pheight_smult_smult divide_inverse mult.commute)
  have cd: "c / of_int ?d \<noteq> 0" using c d by simp
  show ?thesis unfolding pheight_integral_rep_def
    using cd eq3 by blast
qed

lemma pheight_primitive_rep_exists:
  fixes P :: "rat mpoly"
  assumes p: "P \<noteq> 0"
  shows "\<exists>Q::int mpoly. pheight_integral_rep P Q \<and> Q \<noteq> 0 \<and> primitive Q"
proof -
  obtain Q::"int mpoly" where rep: "pheight_integral_rep P Q"
    using pheight_integral_rep_exists[of P] by blast
  obtain c::rat where c: "c \<noteq> 0" and eq: "replace_coeff of_int Q = smult c P"
    using rep by (auto simp: pheight_integral_rep_def)
  have cast0: "(replace_coeff of_int (0::int mpoly) :: rat mpoly) = 0"
    using replace_coeff_monom[of of_int 0 0] by simp
  have q: "Q \<noteq> 0"
    using eq pheight_smult_nonzero_rat[OF c p] cast0 by auto
  have v: "sdiv (Gcd (coeffs Q)) Q \<noteq> 0"
    using q pheight_content_sdiv[of Q] by (auto simp: smult_conv_mult)
  show ?thesis using pheight_integral_rep_sdiv[OF rep q] pheight_sdiv_primitive[OF q] v by blast
qed

lemma pheight_proj_height_primitive_rep:
  fixes P :: "rat mpoly" and Q :: "int mpoly"
  assumes p: "P \<noteq> 0" and q: "Q \<noteq> 0" and prim: "primitive Q" and rep: "pheight_integral_rep P Q"
  shows "pheight_proj_height P = pheight_int_coeff_sup Q"
proof -
  obtain c::rat where c: "c \<noteq> 0" and eq: "replace_coeff of_int Q = smult c P"
    using rep by (auto simp: pheight_integral_rep_def)
  have h: "pheight_proj_height (replace_coeff of_int Q) = pheight_proj_height P"
    using eq pheight_proj_height_smult[OF c, of P] by simp
  show ?thesis
    using h pheight_proj_height_cast_primitive[OF q prim] by simp
qed

lemma pheight_cast_mult:
  fixes P Q :: "int mpoly"
  shows "(replace_coeff of_int (P*Q) :: rat mpoly) =replace_coeff of_int P * replace_coeff of_int Q"
  by (rule pjet_replace_coeff_mult) simp_all

lemma pheight_integral_rep_mult:
  fixes P Q :: "rat mpoly" and U V :: "int mpoly"
  assumes "pheight_integral_rep P U" "pheight_integral_rep Q V"
  shows "pheight_integral_rep (P*Q) (U*V)"
proof -
  obtain c d where c: "c \<noteq> 0" and ceq: "replace_coeff of_int U = smult c P"
    and d: "d \<noteq> 0" and deq: "replace_coeff of_int V = smult d Q"
    using assms by (auto simp: pheight_integral_rep_def)
  have eq: "(replace_coeff of_int (U*V) :: rat mpoly) = smult (c*d) (P*Q)"
    using ceq deq
    by (simp add: pheight_cast_mult mult_smult_left smult_conv_mult mult_monom algebra_simps)
  have cd: "c*d \<noteq> 0" using c d by simp
  show ?thesis unfolding pheight_integral_rep_def
    using cd eq by blast
qed

lemma pheight_vars_integral_rep:
  fixes P :: "rat mpoly" and U :: "int mpoly"
  assumes "pheight_integral_rep P U"
  shows "vars U = vars P"
using assms by (metis pheight_integral_rep_def pheight_vars_cast pheight_vars_smult_rat)

lemma pheight_proj_height_disjoint_mult:
  fixes P Q :: "rat mpoly"
  assumes p: "P \<noteq> 0" and q: "Q \<noteq> 0"
    and disj: "vars P \<inter> vars Q = {}"
  shows "pheight_proj_height (P*Q) = pheight_proj_height P * pheight_proj_height Q"
proof -
  obtain U::"int mpoly" where
    urep: "pheight_integral_rep P U" and u: "U \<noteq> 0"
    and uprim: "primitive U"
    using pheight_primitive_rep_exists[OF p] by blast
  obtain V::"int mpoly" where
    vrep: "pheight_integral_rep Q V" and v: "V \<noteq> 0"
    and vprim: "primitive V"
    using pheight_primitive_rep_exists[OF q] by blast
  have duv: "vars U \<inter> vars V = {}"
    using disj pheight_vars_integral_rep[OF urep] pheight_vars_integral_rep[OF vrep] by simp
  have uvprim: "primitive (U*V)"
    by (rule pheight_primitive_disjoint_mult[OF duv uprim vprim])
  have uvrep: "pheight_integral_rep (P*Q) (U*V)"
    by (rule pheight_integral_rep_mult[OF urep vrep])
  have h1: "pheight_proj_height (P*Q) = pheight_int_coeff_sup (U*V)"
    by (simp add: p q pheight_proj_height_primitive_rep u uvprim uvrep v)
  have h2: "pheight_proj_height P = pheight_int_coeff_sup U"
    by (rule pheight_proj_height_primitive_rep[OF p u uprim urep])
  have h3: "pheight_proj_height Q = pheight_int_coeff_sup V"
    by (rule pheight_proj_height_primitive_rep[OF q v vprim vrep])
  show ?thesis
    using h1 h2 h3 pheight_int_coeff_sup_disjoint_mult[OF duv u v]
    by simp
qed

lemma pheight_proj_log_height_disjoint_mult:
  fixes P Q :: "rat mpoly"
  assumes p: "P \<noteq> 0" and q: "Q \<noteq> 0"
    and disj: "vars P \<inter> vars Q = {}"
  shows "pheight_proj_log_height (P*Q) = pheight_proj_log_height P + pheight_proj_log_height Q"
  using pheight_proj_height_disjoint_mult[OF assms]
    pheight_proj_height_ge_one[of P]
    pheight_proj_height_ge_one[of Q]
  by (simp add: pheight_proj_log_height_def ln_mult)

lemma pheight_proj_log_height_disjoint_factor_le:
  fixes P Q :: "rat mpoly"
  assumes p: "P \<noteq> 0" and q: "Q \<noteq> 0"
    and disj: "vars P \<inter> vars Q = {}"
  shows "pheight_proj_log_height P \<le> pheight_proj_log_height (P*Q)"
  using pheight_proj_log_height_disjoint_mult[OF assms]
    pheight_proj_log_height_nonneg[of Q]
  by simp

end
