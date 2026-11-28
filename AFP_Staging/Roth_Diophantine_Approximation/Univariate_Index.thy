theory Univariate_Index
  imports
    "Multivariate_Polynomial_Heights.Polynomial_Heights"
    Disjoint_Index
    Polynomials.MPoly_Type_Univariate
    Berlekamp_Zassenhaus.Mahler_Measure
    Polynomial_Factorization.Kronecker_Factorization
begin

section \<open>The one-variable polynomial representations\<close>

lemma roth_mpoly_to_poly_cast:
  fixes U :: "int mpoly"
  shows "mpoly_to_poly v (replace_coeff of_int U :: rat mpoly) =
         map_poly of_int (mpoly_to_poly v U)"
  by (simp add: poly_eq_iff coeff_map_poly coeff_replace_coeff)

lemma roth_mpoly_to_poly_smult:
  fixes U :: "rat mpoly"
  shows "mpoly_to_poly v (MPoly_Type.smult c U) = Polynomial.smult c (mpoly_to_poly v U)"
  by (simp add: poly_eq_iff pjet_coeff_smult_rat)

lemma roth_vars_poly_to_mpoly:
  fixes Q :: "'a::comm_ring_1 poly"
  shows "vars (poly_to_mpoly v Q) \<subseteq> {v}"
proof
  fix x
  assume x: "x \<in> vars (poly_to_mpoly v Q)"
  then obtain I where ik: "I \<in> Poly_Mapping.keys (mapping_of (poly_to_mpoly v Q))"
       and xk: "x \<in> Poly_Mapping.keys I"
    by (auto simp: vars_def)
  have h: "Poly_Mapping.lookup (mapping_of (poly_to_mpoly v Q)) I
         = (coeff Q (Poly_Mapping.lookup I v) when Poly_Mapping.keys I \<subseteq> {v})"
    unfolding poly_to_mpoly_def
    by (simp add: MPoly_inverse lookup_Abs_poly_mapping[OF poly_to_mpoly_finite])
  have sub: "Poly_Mapping.keys I \<subseteq> {v}"
    using ik h
    by (auto simp: in_keys_iff when_def split: if_splits)
  show "x \<in> {v}" using sub xk by auto
qed

lemma roth_coeffs_poly_to_mpoly:
  fixes Q :: "int poly"
  shows "MPoly_Type.coeffs (poly_to_mpoly v Q) = set (Polynomial.coeffs Q) - {0}"
proof (rule equalityI)
  show "MPoly_Type.coeffs (poly_to_mpoly v Q) \<subseteq> set (Polynomial.coeffs Q) - {0}"
  proof
    fix x
    assume x: "x \<in> MPoly_Type.coeffs (poly_to_mpoly v Q)"
    then obtain I where
      ik: "I \<in> Poly_Mapping.keys (mapping_of (poly_to_mpoly v Q))"
      and xeq: "x = MPoly_Type.coeff (poly_to_mpoly v Q) I"
      by (auto simp: pheight_coeffs_eq)
    have sub: "Poly_Mapping.keys I \<subseteq> {v}"
      using ik roth_vars_poly_to_mpoly[of v Q]
      by (auto simp: vars_def)
    have xeq2: "x = Polynomial.coeff Q (Poly_Mapping.lookup I v)"
      using xeq sub
      unfolding MPoly_Type.coeff_def poly_to_mpoly_def
      by (simp add: MPoly_inverse lookup_Abs_poly_mapping[OF poly_to_mpoly_finite])
    have xnz: "x \<noteq> 0" using ik xeq
      by (simp add: MPoly_Type.coeff_def in_keys_iff)
    show "x \<in> set (Polynomial.coeffs Q) - {0}"
      using xeq2 xnz range_coeff[of Q] by auto
  qed
  show "set (Polynomial.coeffs Q) - {0} \<subseteq> MPoly_Type.coeffs (poly_to_mpoly v Q)"
  proof
    fix x
    assume x: "x \<in> set (Polynomial.coeffs Q) - {0}"
    obtain k where xeq: "x = Polynomial.coeff Q k"
      using x range_coeff[of Q] by auto
    have xnz: "x \<noteq> 0" using x by auto
    have h: "MPoly_Type.coeff (poly_to_mpoly v Q) (Poly_Mapping.single v k) = x"
      using xeq by (simp add: coeff_poly_to_mpoly)
    have ik: "Poly_Mapping.single v k \<in> Poly_Mapping.keys (mapping_of (poly_to_mpoly v Q))"
      using h xnz by (simp add: MPoly_Type.coeff_def in_keys_iff)
    show "x \<in> MPoly_Type.coeffs (poly_to_mpoly v Q)"
      using ik h by (auto simp: pheight_coeffs_eq)
  qed
qed

lemma roth_Gcd_remove_zero_int:
  fixes A :: "int set"
  shows "Gcd (A - {0}) = Gcd A"
  by (metis Gcd_insert gcd.top_left_normalize insert_Diff_single normalize_Gcd)

lemma roth_content_poly_to_mpoly:
  fixes Q :: "int poly"
  shows "Gcd (MPoly_Type.coeffs (poly_to_mpoly v Q)) = Polynomial.content Q"
  by (simp add: roth_coeffs_poly_to_mpoly roth_Gcd_remove_zero_int Polynomial.content_def)

lemma roth_primitive_poly_to_mpoly:
  fixes Q :: "int poly"
  shows "MPoly_Type.primitive (poly_to_mpoly v Q) \<longleftrightarrow> Polynomial.content Q = 1"
  by (simp add: MPoly_Type.primitive_def roth_content_poly_to_mpoly)

lemma roth_content_mpoly_to_poly:
  fixes U :: "int mpoly"
  assumes "vars U \<subseteq> {v}"
  shows "Polynomial.content (mpoly_to_poly v U) = Gcd (MPoly_Type.coeffs U)"
  using roth_content_poly_to_mpoly mpoly_to_poly_inverse[OF assms] by metis

lemma roth_primitive_mpoly_to_poly:
  fixes U :: "int mpoly"
  assumes "vars U \<subseteq> {v}"
  shows "Polynomial.content (mpoly_to_poly v U) = 1 \<longleftrightarrow> MPoly_Type.primitive U"
  by (simp add: roth_content_mpoly_to_poly[OF assms] MPoly_Type.primitive_def)

lemma roth_int_coeff_sup_poly_coeff:
  fixes Q :: "int poly"
  shows "nat (\<bar>Polynomial.coeff Q k\<bar>) \<le> pheight_int_coeff_sup (poly_to_mpoly v Q)"
  by (metis coeff_poly_to_mpoly pheight_int_coeff_sup_coeff)

lemma roth_int_coeff_sup_poly_coeffs:
  fixes Q :: "int poly"
  assumes "c \<in> set (Polynomial.coeffs Q)"
  shows "nat (\<bar>c\<bar>) \<le> pheight_int_coeff_sup (poly_to_mpoly v Q)"
proof -
  obtain k where "c = Polynomial.coeff Q k"
    using assms range_coeff[of Q] by auto
  then show ?thesis
    using roth_int_coeff_sup_poly_coeff by simp
qed

lemma roth_poly_to_mpoly_nonzero:
  fixes Q :: "'a::comm_ring_1 poly"
  assumes "Q \<noteq> 0"
  shows "poly_to_mpoly v Q \<noteq> 0"
  by (metis assms poly_to_mpoly_inverse poly_to_mpoly_inverse poly_to_mpoly0)

lemma roth_mpoly_to_poly_nonzero:
  fixes U :: "'a::comm_ring_1 mpoly"
  assumes u: "U \<noteq> 0" and uv: "vars U \<subseteq> {v}"
  shows "mpoly_to_poly v U \<noteq> 0"
  using u mpoly_to_poly_inverse[OF uv] poly_to_mpoly0
  by metis

section \<open>Mahler measure of a rational point\<close>

lemma roth_linear_cast_complex:
  fixes p q :: int
  assumes q: "q \<noteq> 0"
  shows "(map_poly of_int [:-p,q:] :: complex poly) =
    smult (of_int q) [:- (of_int p / of_int q), 1:]"
  using q by auto

lemma roth_mahler_smult_linear:
  fixes c a :: complex
  shows "mahler_measure_poly (smult c [:-a,1:]) = cmod c * max 1 (cmod a)"
  using mahler_measure_poly_explicit[of c "[a]"] by simp

lemma roth_mahler_linear_pre:
  fixes p q :: int
  assumes q: "q \<noteq> 0"
  shows "mahler_measure [:-p,q:] = of_int \<bar>q\<bar> * max 1 (of_int (\<bar>p\<bar>) / of_int \<bar>q\<bar>)"
proof -
  have e: "(map_poly of_int [:-p,q:] :: complex poly) =
    smult (of_int q) [:- (of_int p / of_int q), 1:]"
    by (rule roth_linear_cast_complex[OF q])
  show ?thesis
    unfolding mahler_measure_def e roth_mahler_smult_linear
    by (simp add: norm_divide)
qed

lemma roth_mahler_linear:
  fixes p q :: int
  assumes q: "q > 0"
  shows "mahler_measure [:-p,q:] = of_int (max (\<bar>p\<bar>) q)"
  using roth_mahler_linear_pre[of q p] q
  by (simp add: max_mult_distrib_left)

lemma roth_mahler_mult:
  shows "mahler_measure (Q*R) = mahler_measure Q * mahler_measure R"
  unfolding mahler_measure_def of_int_poly_hom.hom_mult
  by (rule measure_eq_prod)

lemma roth_mahler_one: "mahler_measure 1 = 1"
  by (simp add: mahler_measure_def mahler_measure_poly_def)

lemma roth_mahler_power:
  shows "mahler_measure (Q^n) = mahler_measure Q ^n"
  by (induction n) (simp_all add: roth_mahler_one roth_mahler_mult)

lemma roth_linear_content:
  fixes p q :: int
  assumes "coprime p q"
  shows "Polynomial.content [:-p,q:] = 1"
  using assms by (simp add: coprime_commute)

lemma roth_linear_cast_rat:
  fixes p q :: int
  assumes q: "q \<noteq> 0"
  shows "(map_poly of_int [:-p,q:] :: rat poly) = smult (of_int q) [:- Rat.Fract p q, 1:]"
  using q by (simp add: Rat.Fract_of_int_quotient)

lemma roth_linear_power_content:
  fixes p q :: int
  assumes "coprime p q"
  shows "Polynomial.content ([:-p,q:] ^ n) = 1"
  by (induction n)
    (simp_all only: power_0 power_Suc content_1 content_mult
      roth_linear_content[OF assms] mult_1_left mult_1_right)

lemma roth_linear_power_cast_rat:
  fixes p q :: int
  assumes q: "q \<noteq> 0"
  shows "map_poly of_int ([:-p,q:] ^ n) = smult ((of_int q)^n) ([:- Rat.Fract p q,1:]^n)"
  unfolding of_int_poly_hom.hom_power roth_linear_cast_rat[OF q] smult_power by simp

lemma roth_linear_power_cast_dvd:
  fixes q :: "int"
  assumes q: "q \<noteq> 0"
  shows "((map_poly of_int ([:-p,q:] ^ n) :: rat poly) dvd map_poly of_int Q) =
         ([:-Rat.Fract p q,1:] ^ n dvd map_poly of_int Q)"
  unfolding roth_linear_power_cast_rat[OF q]
  using q by (simp add: smult_dvd_iff)

lemma roth_linear_power_dvd:
  fixes q :: int
  assumes q: "q \<noteq> 0" and cpq: "coprime p q" and Q: "Q \<noteq> 0"
  shows "[:-p,q:] ^ n dvd Q \<longleftrightarrow> n \<le> Polynomial.order (Rat.Fract p q) (map_poly of_int Q :: rat poly)"
proof -
  have "([:-p,q:] ^ n dvd Q)
      = ((map_poly of_int ([:-p,q:] ^ n) :: rat poly) dvd map_poly of_int Q)"
    by (rule dvd_poly_int_content_1 [OF roth_linear_power_content[OF cpq]])
  also have "\<dots> = ([:-Rat.Fract p q,1:] ^ n dvd map_poly of_int Q)"
    by (rule roth_linear_power_cast_dvd[OF q])
  also have "\<dots> = (n \<le> Polynomial.order (Rat.Fract p q) (map_poly of_int Q))"
    using Q order_divides by blast
  finally show ?thesis by simp
qed

lemma roth_mahler_order_le:
  fixes q :: int
  assumes q: "q > 0" and cpq: "coprime p q" and Q: "Q \<noteq> 0"
  shows "of_int (max (\<bar>p\<bar>) q) ^ Polynomial.order (Rat.Fract p q) (map_poly of_int Q :: rat poly)
      \<le> mahler_measure Q"
proof -
  let ?l = "Polynomial.order (Rat.Fract p q) (map_poly of_int Q)"
  have dvd: "[:-p,q:] ^ ?l dvd Q"
    using Q cpq q roth_linear_power_dvd by force
  with mahler_measure_dvd[OF Q dvd] show ?thesis
    by (simp add: roth_mahler_linear[OF q] roth_mahler_power)
qed

lemma roth_coprime_bridge:
  fixes p q :: int
  assumes "coprime p q"
  shows "algebraic_semidom_class.coprime p q"
  using assms by (simp add: coprime_iff_gcd_eq_1)

lemma roth_rat_height_order_le:
  fixes Q :: "int poly"
  assumes q: "q > (0::int)"
    and cpq: "coprime p q"
    and Q: "Q \<noteq> 0"
  shows "real (pheight_rat_height (Rat.Fract p q)) ^ Polynomial.order (Rat.Fract p q) (map_poly of_int Q)
       \<le> mahler_measure Q"
  using roth_mahler_order_le[OF q cpq Q]
    pheight_rat_height_Fract[OF q roth_coprime_bridge[OF cpq]] q
  by simp

lemma roth_coeff_square_le:
  fixes Q :: "int poly"
  assumes a: "a \<in> set (Polynomial.coeffs Q)"
  shows "a*a \<le> int (pheight_int_coeff_sup (poly_to_mpoly v Q)) ^ 2"
proof -
  have h: "\<bar>a\<bar> \<le> int (pheight_int_coeff_sup (poly_to_mpoly v Q))"
    using roth_int_coeff_sup_poly_coeffs[OF a, of v] by simp
  then show ?thesis
    by (metis abs_le_square_iff abs_of_nat power2_eq_square)
qed

lemma roth_coeff_square_sum_le:
  fixes Q :: "int poly"
  shows "(\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a) \<le>
    int (length (Polynomial.coeffs Q)) * int (pheight_int_coeff_sup (poly_to_mpoly v Q)) ^ 2"
proof -
  have "(\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a) \<le>
        (\<Sum>a\<leftarrow>Polynomial.coeffs Q. int (pheight_int_coeff_sup (poly_to_mpoly v Q)) ^ 2)"
    by (rule sum_list_mono) (rule roth_coeff_square_le)
  also have "\<dots> =
    int (length (Polynomial.coeffs Q)) * int (pheight_int_coeff_sup (poly_to_mpoly v Q)) ^ 2"
    by (simp add: map_replicate_const sum_list_replicate)
  finally show ?thesis .
qed

lemma roth_cast_square_id:
  "real_of_int (int n * int H^2) = real n * (real H)^2"
  by simp

lemma roth_mahler_coeff_sup_le:
  fixes Q :: "int poly"
  shows "mahler_measure Q \<le>
         sqrt (length (Polynomial.coeffs Q)) * pheight_int_coeff_sup (poly_to_mpoly v Q)"
proof -
  have "mahler_measure Q \<le> sqrt (\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a)"
    by (rule Landau_inequality_mahler_measure)
  also have "... \<le> sqrt (real (length (Polynomial.coeffs Q)) * real (pheight_int_coeff_sup (poly_to_mpoly v Q)) ^ 2)"
    using real_sqrt_le_mono roth_coeff_square_sum_le
    by (metis (no_types, lifting) of_int_le_iff roth_cast_square_id)
  also have "... = sqrt (real (length (Polynomial.coeffs Q))) * real (pheight_int_coeff_sup (poly_to_mpoly v Q))"
    by (simp add: real_sqrt_mult)
  finally show ?thesis .
qed

lemma roth_sqrt_suc_le_exp:
  "sqrt (real (Suc n)) \<le> exp (real n)"
proof -
  have "sqrt (real (Suc n)) \<le> real (Suc n)"
    by (simp add: real_le_lsqrt self_le_power)
  then show ?thesis
    by (metis exp_ge_add_one_self of_nat_Suc order.trans)
qed

lemma roth_mahler_exp_degree_le:
  fixes Q :: "int poly"
  assumes Q: "Q \<noteq> 0"
  shows "mahler_measure Q \<le> exp (real (degree Q)) * real (pheight_int_coeff_sup (poly_to_mpoly v Q))"
  using roth_mahler_coeff_sup_le roth_sqrt_suc_le_exp Q
  by (smt (verit, best) length_coeffs_degree mult_right_mono of_nat_0_le_iff)

lemma roth_univariate_log_order_bound:
  fixes Q :: "int poly"
  assumes q: "q > 0" and cpq: "coprime p q" and Q: "Q \<noteq> 0"
  shows "Polynomial.order (Rat.Fract p q) (map_poly of_int Q :: rat poly) *
         pheight_rat_log_height (Rat.Fract p q)
    \<le> ln (real (pheight_int_coeff_sup (poly_to_mpoly v Q))) + real (degree Q)"
proof -
  let ?H = "real (pheight_rat_height (Rat.Fract p q))"
  let ?C = "real (pheight_int_coeff_sup (poly_to_mpoly v Q))"
  let ?l = "Polynomial.order (Rat.Fract p q) (map_poly of_int Q)"
  have b: "?H ^ ?l \<le> exp (real (degree Q)) * ?C"
    using Q roth_rat_height_order_le[OF q cpq] roth_mahler_exp_degree_le
    by (meson order_trans)
  have "ln (?H ^ ?l) \<le> ln (exp (real (degree Q)) * ?C)"
    using b by simp
  then show ?thesis
    by (simp add: ln_realpow ln_mult_pos pheight_rat_log_height_def mult.commute)
qed

section \<open>The bound for rational univariate polynomials\<close>

lemma roth_rat_fraction_exists:
  fixes x :: rat
  shows "\<exists>p q::int. q > 0 \<and> coprime p q \<and> x = Rat.Fract p q"
  by (metis Rat_cases coprime_iff_coprime)

lemma roth_rat_poly_primitive_rep:
  fixes P :: "rat poly"
  assumes p: "P \<noteq> 0"
  shows "\<exists>Q::int poly. \<exists>c::rat.
    Q \<noteq> 0 \<and> Polynomial.content Q = 1 \<and> c \<noteq> 0 \<and>
    map_poly of_int Q = Polynomial.smult c P \<and>
    pheight_proj_height (poly_to_mpoly v P) = pheight_int_coeff_sup (poly_to_mpoly v Q)"
proof -
  have pmp: "poly_to_mpoly v P \<noteq> 0"
    by (rule roth_poly_to_mpoly_nonzero[OF p])
  obtain U where rep: "pheight_integral_rep (poly_to_mpoly v P) U"
    and u: "U \<noteq> 0" and prim: "MPoly_Type.primitive U"
    using pheight_primitive_rep_exists[OF pmp] by blast
  then have uv: "vars U \<subseteq> {v}"
    using pheight_vars_integral_rep roth_vars_poly_to_mpoly by blast
  let ?Q = "mpoly_to_poly v U"
  have un: "poly_to_mpoly v ?Q = U"
    by (rule mpoly_to_poly_inverse[OF uv])
  have qnz: "?Q \<noteq> 0"
    by (rule roth_mpoly_to_poly_nonzero[OF u uv])
  have qprim: "Polynomial.content ?Q = 1"
    using roth_primitive_mpoly_to_poly[OF uv] prim by simp
  obtain c::rat where cnz: "c \<noteq> 0" and
    eq: "(replace_coeff of_int U :: rat mpoly) = MPoly_Type.smult c (poly_to_mpoly v P)"
    using rep by (auto simp: pheight_integral_rep_def)
  have eqpoly: "map_poly of_int ?Q = Polynomial.smult c P"
    using eq
    by (metis poly_to_mpoly_inverse roth_mpoly_to_poly_cast roth_mpoly_to_poly_smult)
  have height: "pheight_proj_height (poly_to_mpoly v P) = pheight_int_coeff_sup (poly_to_mpoly v ?Q)"
    using pheight_proj_height_primitive_rep[OF pmp u prim rep] un by simp
  show ?thesis using qnz qprim cnz eqpoly height by blast
qed

lemma roth_univariate_rat_poly_log_order_bound:
  fixes P :: "rat poly"
  assumes P: "P \<noteq> 0"
  shows "real (Polynomial.order \<beta> P) * pheight_rat_log_height \<beta> \<le>
    pheight_proj_log_height (poly_to_mpoly v P) + real (degree P)"
proof -
  obtain p q::int where qpos: "q > 0" and cpq: "coprime p q"
    and beq: "\<beta> = Rat.Fract p q"
    using roth_rat_fraction_exists[of \<beta>] by blast
  obtain Q::"int poly" and c::rat where
    Qnz: "Q \<noteq> 0" and Qprim: "Polynomial.content Q = 1"
    and cnz: "c \<noteq> 0"
    and eq: "map_poly of_int Q = Polynomial.smult c P"
    and height: "pheight_proj_height (poly_to_mpoly v P) = pheight_int_coeff_sup (poly_to_mpoly v Q)"
    using roth_rat_poly_primitive_rep[OF P] by blast
  have ord: "Polynomial.order \<beta> (map_poly of_int Q :: rat poly) = Polynomial.order \<beta> P"
    using eq cnz by (simp add: Polynomial.order_smult)
  have degcast: "degree (map_poly of_int Q :: rat poly) = degree Q"
    by (rule degree_map_poly) simp
  then have deg: "degree Q = degree P"
    using eq cnz by simp
  have h: "pheight_proj_log_height (poly_to_mpoly v P) = ln (real (pheight_int_coeff_sup (poly_to_mpoly v Q)))"
    using height by (simp add: pheight_proj_log_height_def)
  note b = roth_univariate_log_order_bound[OF qpos cpq Qnz, of v]
  show ?thesis using b beq ord deg h by metis
qed

lemma roth_univariate_mpoly_log_order_bound:
  fixes P :: "rat mpoly"
  assumes P: "P \<noteq> 0" and pv: "vars P \<subseteq> {v}"
  shows "real (Polynomial.order \<beta> (mpoly_to_poly v P)) * pheight_rat_log_height \<beta>
       \<le> pheight_proj_log_height P + real (degree (mpoly_to_poly v P))"
proof -
  have pn: "mpoly_to_poly v P \<noteq> 0"
    by (rule roth_mpoly_to_poly_nonzero[OF P pv])
  have peq: "poly_to_mpoly v (mpoly_to_poly v P) = P"
    by (rule mpoly_to_poly_inverse[OF pv])
  show ?thesis
    using roth_univariate_rat_poly_log_order_bound[OF pn, of \<beta> v] peq by simp
qed

section \<open>Univariate order and the Roth index\<close>

lemma roth_translate_poly_to_mpoly:
  fixes p :: "rat poly"
  shows "pjet_translate a (poly_to_mpoly v p) = poly_to_mpoly v (pcompose p [:a v,1:])"
proof -
  have vl: "vars (pjet_translate a (poly_to_mpoly v p)) \<subseteq> {v}"
    using pjet_vars_translate_subset roth_vars_poly_to_mpoly[of v p]
    by blast
  have aux: "insertion (\<lambda>_. x) (pjet_translate a (poly_to_mpoly v p))
           = insertion (\<lambda>u. x + a u) (poly_to_mpoly v p)" for x
    by (simp add: pjet_translate_def pjet_insertion_subst insertion_add)
  have aux2: "insertion (\<lambda>u. x + a u) (poly_to_mpoly v p)
            = insertion (\<lambda>_. x + a v) (poly_to_mpoly v p)" for x
    using roth_vars_poly_to_mpoly by (intro insertion_irrelevant_vars) auto
  have eval: "poly (mpoly_to_poly v (pjet_translate a (poly_to_mpoly v p))) x = poly p (x + a v)" for x
    using aux aux2 poly_eq_insertion[OF vl] poly_eq_insertion[OF roth_vars_poly_to_mpoly]
      poly_to_mpoly_inverse
    by metis
  have peq: "mpoly_to_poly v (pjet_translate a (poly_to_mpoly v p)) = pcompose p [:a v,1:]"
    by (simp add: add.commute eval poly_ext poly_pcompose)
  show ?thesis using peq mpoly_to_poly_inverse[OF vl] by simp
qed

lemma roth_order_zero_coeff:
  fixes p :: "rat poly"
  assumes p: "p \<noteq> 0"
  shows "(\<forall>k<Polynomial.order 0 p. coeff p k = 0) \<and> coeff p (Polynomial.order 0 p) \<noteq> 0"
proof -
  let ?l = "Polynomial.order 0 p"
  obtain ld: "monom 1 ?l dvd p" and nd: "\<not> monom 1 (Suc ?l) dvd p"
    using Suc_n_not_le_n monom_1_dvd_iff p by blast
  have low: "\<forall>k<?l. coeff p k = 0"
    using ld by (simp add: monom_1_dvd_iff')
  have high: "coeff p ?l \<noteq> 0"
    using low nd by (auto simp: monom_1_dvd_iff' dest: less_SucE)
  show ?thesis using low high by blast
qed

lemma roth_order_shift:
  fixes p :: "rat poly"
  assumes p: "p \<noteq> 0"
  shows "Polynomial.order 0 (pcompose p [:\<beta>,1:]) = Polynomial.order \<beta> p"
proof -
  obtain q where peq: "p = [:-\<beta>,1:] ^ Polynomial.order \<beta> p * q"
    and qnd: "\<not> [:-\<beta>,1:] dvd q"
    using order_decomp[OF p, of \<beta>] by blast
  have q0: "poly q \<beta> \<noteq> 0"
    using qnd by (simp add: poly_eq_0_iff_dvd)
  have lin: "pcompose [:-\<beta>,1:] [:\<beta>,1:] = [:0,1:]"
    by auto
  have cpow: "pcompose ([:-\<beta>,1:] ^ n) [:\<beta>,1:] = [:0,1:] ^ n" for n
    by (induction n) (simp_all only: power_0 power_Suc pcompose_mult pcompose_1 lin)
  have mid: "pcompose (([:-\<beta>,1:] ^ Polynomial.order \<beta> p) * q) [:\<beta>,1:] =
             monom 1 (Polynomial.order \<beta> p) * pcompose q [:\<beta>,1:]"
    by (simp only: pcompose_mult cpow monom_altdef smult_1_left)
  have shift: "pcompose p [:\<beta>,1:] = monom 1 (Polynomial.order \<beta> p) * pcompose q [:\<beta>,1:]"
    using mid peq by metis
  have qshift: "pcompose q [:\<beta>,1:] \<noteq> 0"
    using q0 p pcompose_eq_0_iff shift by force
  have qord: "Polynomial.order 0 (pcompose q [:\<beta>,1:]) = 0"
    by (rule order_0I) (simp add: poly_pcompose q0)
  have nz: "monom 1 (Polynomial.order \<beta> p) * pcompose q [:\<beta>,1:] \<noteq> 0"
    using qshift by simp
  show ?thesis
    using shift qord nz by (simp add: Polynomial.order_mult)
qed

lemma roth_univariate_taylor_coeff:
  fixes p :: "rat poly"
  shows "pjet_taylor_coeff a (Poly_Mapping.single v k) (poly_to_mpoly v p) =
    Polynomial.coeff (pcompose p [:a v,1:]) k"
  by (simp add: pjet_taylor_coeff_def roth_translate_poly_to_mpoly coeff_poly_to_mpoly)

lemma roth_univariate_taylor_support:
  fixes p :: "rat poly"
  assumes "pjet_taylor_coeff a I (poly_to_mpoly v p) \<noteq> 0"
  shows "I = Poly_Mapping.single v (Poly_Mapping.lookup I v)"
proof -
  have vin: "Poly_Mapping.keys I \<subseteq> vars (pjet_translate a (poly_to_mpoly v p))"
    using assms by (auto simp: pjet_taylor_coeff_key vars_def)
  have kv: "Poly_Mapping.keys I \<subseteq> {v}"
    using roth_vars_poly_to_mpoly pjet_vars_translate_subset vin by blast
  show ?thesis
    by (simp add: keys_subset_singleton_imp_monomial kv)
qed

lemma roth_univariate_index_order:
  fixes p :: "rat poly" and r :: "nat \<Rightarrow> nat"
  assumes p: "p \<noteq> 0" and r: "r 0 > 0"
  shows "roth_index 1 r (\<lambda>_. \<beta>) (poly_to_mpoly 0 p) =
    ereal (real (Polynomial.order \<beta> p) / real (r 0))"
proof -
  let ?s = "pcompose p [:\<beta>,1:]"
  let ?l = "Polynomial.order \<beta> p"
  have snz: "?s \<noteq> 0"
    using p by (simp add: pcompose_eq_0_iff)
  have low: "\<forall>k<?l. Polynomial.coeff ?s k = 0" and high: "Polynomial.coeff ?s ?l \<noteq> 0"
    using roth_order_zero_coeff[OF snz] roth_order_shift[OF p] by auto
  have pmp: "poly_to_mpoly 0 p \<noteq> 0"
    by (rule roth_poly_to_mpoly_nonzero[OF p])
  obtain I where tc: "pjet_taylor_coeff (\<lambda>_. \<beta>) I (poly_to_mpoly 0 p) \<noteq> 0"
           and ieq: "roth_index 1 r (\<lambda>_. \<beta>) (poly_to_mpoly 0 p) = ereal (roth_weight 1 r I)"
    using roth_index_attained[OF pmp] by blast
  have "I = Poly_Mapping.single 0 (Poly_Mapping.lookup I 0)"
    by (rule roth_univariate_taylor_support[OF tc])
  then have "Polynomial.coeff ?s (Poly_Mapping.lookup I 0) \<noteq> 0"
    using tc roth_univariate_taylor_coeff by metis
  then have lk: "?l \<le> Poly_Mapping.lookup I 0"
    using low by (metis not_le_imp_less)
  have wI: "roth_weight 1 r I = real (Poly_Mapping.lookup I 0) / r 0"
    by (simp add: roth_weight_def)
  have w: "roth_weight 1 r (Poly_Mapping.single 0 ?l) = real ?l / real (r 0)"
    by (simp add: roth_weight_def)
  have tcl: "pjet_taylor_coeff (\<lambda>_. \<beta>) (Poly_Mapping.single 0 ?l) (poly_to_mpoly 0 p) \<noteq> 0"
    using high by (simp add: roth_univariate_taylor_coeff)
  have "roth_index 1 r (\<lambda>_. \<beta>) (poly_to_mpoly 0 p) \<le> ereal (real ?l / r 0)"
    using roth_index_le_coeff[OF tcl, of 1 r] w by metis
  also have "\<dots> \<le> roth_index 1 r (\<lambda>_. \<beta>) (poly_to_mpoly 0 p)"
    using ieq wI lk r by (simp add: roth_weight_def divide_right_mono)
  finally show ?thesis .
qed

lemma roth_univariate_index_bound:
  fixes p :: "rat poly" and r :: "nat \<Rightarrow> nat"
  assumes p: "p \<noteq> 0" and r: "r 0 > 0"
    and deg: "degree p \<le> r 0" and \<eta>: "\<eta> > 0"
    and h: "pheight_proj_log_height (poly_to_mpoly 0 p) + real (r 0)
          \<le> \<eta> * real (r 0) * pheight_rat_log_height \<beta>"
  shows "roth_index 1 r (\<lambda>_. \<beta>) (poly_to_mpoly 0 p) \<le> ereal \<eta>"
proof -
  have posprod: "0 < \<eta> * real (r 0) * pheight_rat_log_height \<beta>"
    using h r pheight_proj_log_height_nonneg[of "poly_to_mpoly 0 p"]
    by linarith
  then have hp: "0 < pheight_rat_log_height \<beta>"
    using less_eq_real_def posprod pheight_rat_log_height_nonneg by force
  have b: "real (Polynomial.order \<beta> p) * pheight_rat_log_height \<beta> \<le>
           pheight_proj_log_height (poly_to_mpoly 0 p) + degree p"
    by (rule roth_univariate_rat_poly_log_order_bound[OF p])
  have l: "real (Polynomial.order \<beta> p) \<le> \<eta> * r 0"
    using b deg h hp mult_le_cancel_right_pos by fastforce
  have ratio: "real (Polynomial.order \<beta> p) / r 0 \<le> \<eta>"
    using l r by (simp add: pos_divide_le_eq)
  show ?thesis
    using roth_univariate_index_order p r ratio by force
qed

lemma roth_univariate_mpoly_index_bound:
  fixes P :: "rat mpoly" and r :: "nat \<Rightarrow> nat"
  assumes P: "P \<noteq> 0" and pv: "vars P \<subseteq> {0}"
    and r: "r 0 > 0"
    and deg: "degree (mpoly_to_poly 0 P) \<le> r 0"
    and \<eta>: "\<eta> > 0"
    and h: "pheight_proj_log_height P + real (r 0) \<le> \<eta> * real (r 0) * pheight_rat_log_height \<beta>"
  shows "roth_index 1 r (\<lambda>_. \<beta>) P \<le> ereal \<eta>"
proof -
  have pn: "mpoly_to_poly 0 P \<noteq> 0"
    by (rule roth_mpoly_to_poly_nonzero[OF P pv])
  have peq: "poly_to_mpoly 0 (mpoly_to_poly 0 P) = P"
    by (rule mpoly_to_poly_inverse[OF pv])
  show ?thesis
    using roth_univariate_index_bound pn peq assms by metis
qed

lemma roth_univariate_vars_of_box:
  fixes P :: "rat mpoly"
  assumes "pjet_poly_in_box 1 r P"
  shows "vars P \<subseteq> {0}"
  using assms by (auto simp: vars_def pjet_poly_in_box_def dest: pjet_exponent_boxD(1))

lemma roth_univariate_degree_of_box:
  fixes P :: "rat mpoly"
  assumes "pjet_poly_in_box 1 r P"
  shows "degree (mpoly_to_poly 0 P) \<le> r 0"
proof (intro degree_le strip)
  fix i assume i: "r 0 < i"
  have outside: "Poly_Mapping.single 0 i \<notin> pjet_exponent_box 1 r"
    using i by (simp add: pjet_exponent_box_iff)
  show "Polynomial.coeff (mpoly_to_poly 0 P) i = 0"
    using pjet_coeff_zero_outside_box[OF assms outside] by simp
qed

theorem roth_lemma_one_variable:
  fixes P :: "rat mpoly" and r :: "nat \<Rightarrow> nat"
  assumes "P \<noteq> 0" and box: "pjet_poly_in_box 1 r P"
    and "r 0 > 0" "\<eta> > 0"
    and "pheight_proj_log_height P + real (r 0)
          \<le> \<eta> * real (r 0) * pheight_rat_log_height \<beta>"
  shows "roth_index 1 r (\<lambda>_. \<beta>) P \<le> ereal \<eta>"
  using roth_univariate_mpoly_index_bound assms
        roth_univariate_vars_of_box[OF box] roth_univariate_degree_of_box[OF box]
  by blast

end
