theory Roth_Rational_Height
  imports
    Roth_Disjoint_Index
    "HOL.Transcendental"
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

end
