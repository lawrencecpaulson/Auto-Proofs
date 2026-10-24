theory Roth_Primitive_Height
  imports Roth_Disjoint_Height Roth_Hasse_Derivative
begin

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
