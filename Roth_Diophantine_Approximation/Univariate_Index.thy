theory Univariate_Index
  imports
    Primitive_Height
    Polynomials.MPoly_Type_Univariate
    Berlekamp_Zassenhaus.Mahler_Measure
    Polynomial_Factorization.Kronecker_Factorization
begin

section \<open>The one-variable polynomial representations\<close>

lemma roth_weight_one:
  fixes r :: "nat \<Rightarrow> nat"
  shows "roth_weight 1 r I =
    real (Poly_Mapping.lookup I 0) / real (r 0)"
  by (simp add: roth_weight_def)

lemma roth_mpoly_to_poly_cast:
  fixes U :: "int mpoly"
  shows "mpoly_to_poly v
    (replace_coeff of_int U :: rat mpoly) =
    map_poly of_int (mpoly_to_poly v U)"
  by (simp add: poly_eq_iff roth_coeff_cast coeff_map_poly)

lemma roth_mpoly_to_poly_smult:
  fixes U :: "rat mpoly"
  shows "mpoly_to_poly v (MPoly_Type.smult c U) =
    Polynomial.smult c (mpoly_to_poly v U)"
  by (simp add: poly_eq_iff roth_coeff_smult_rat coeff_smult)

lemma roth_vars_poly_to_mpoly:
  fixes Q :: "'a::comm_ring_1 poly"
  shows "vars (poly_to_mpoly v Q) \<subseteq> {v}"
proof
  fix x
  assume x: "x \<in> vars (poly_to_mpoly v Q)"
  then obtain I where
    ik: "I \<in> Poly_Mapping.keys
      (mapping_of (poly_to_mpoly v Q))"
    and xk: "x \<in> Poly_Mapping.keys I"
    by (auto simp: vars_def)
  have h: "Poly_Mapping.lookup
    (mapping_of (poly_to_mpoly v Q)) I =
    (coeff Q (Poly_Mapping.lookup I v) when
      Poly_Mapping.keys I \<subseteq> {v})"
    unfolding poly_to_mpoly_def
    by (simp add: MPoly_inverse
      lookup_Abs_poly_mapping[OF poly_to_mpoly_finite])
  have sub: "Poly_Mapping.keys I \<subseteq> {v}"
    using ik h
    by (auto simp: in_keys_iff when_def split: if_splits)
  show "x \<in> {v}" using sub xk by auto
qed

lemma roth_coeffs_poly_to_mpoly:
  fixes Q :: "int poly"
  shows "MPoly_Type.coeffs (poly_to_mpoly v Q) =
    set (Polynomial.coeffs Q) - {0}"
proof (rule equalityI)
  show "MPoly_Type.coeffs (poly_to_mpoly v Q) \<subseteq>
    set (Polynomial.coeffs Q) - {0}"
  proof
    fix x
    assume x: "x \<in> MPoly_Type.coeffs (poly_to_mpoly v Q)"
    then obtain I where
      ik: "I \<in> Poly_Mapping.keys
        (mapping_of (poly_to_mpoly v Q))"
      and xeq: "x = MPoly_Type.coeff (poly_to_mpoly v Q) I"
      by (auto simp: roth_coeffs_eq)
    have sub: "Poly_Mapping.keys I \<subseteq> {v}"
      using ik roth_vars_poly_to_mpoly[of v Q]
      by (auto simp: vars_def)
    have xeq2: "x = Polynomial.coeff Q
      (Poly_Mapping.lookup I v)"
      using xeq sub
      unfolding MPoly_Type.coeff_def poly_to_mpoly_def
      by (simp add: MPoly_inverse
        lookup_Abs_poly_mapping[OF poly_to_mpoly_finite])
    have xnz: "x \<noteq> 0" using ik xeq
      by (simp add: MPoly_Type.coeff_def in_keys_iff)
    show "x \<in> set (Polynomial.coeffs Q) - {0}"
      using xeq2 xnz range_coeff[of Q] by auto
  qed
  show "set (Polynomial.coeffs Q) - {0} \<subseteq>
    MPoly_Type.coeffs (poly_to_mpoly v Q)"
  proof
    fix x
    assume x: "x \<in> set (Polynomial.coeffs Q) - {0}"
    obtain k where xeq: "x = Polynomial.coeff Q k"
      using x range_coeff[of Q] by auto
    have xnz: "x \<noteq> 0" using x by auto
    have h: "MPoly_Type.coeff (poly_to_mpoly v Q)
      (Poly_Mapping.single v k) = x"
      using xeq by (simp add: coeff_poly_to_mpoly)
    have ik: "Poly_Mapping.single v k \<in>
      Poly_Mapping.keys (mapping_of (poly_to_mpoly v Q))"
      using h xnz
      by (simp add: MPoly_Type.coeff_def in_keys_iff)
    show "x \<in> MPoly_Type.coeffs (poly_to_mpoly v Q)"
      using ik h by (auto simp: roth_coeffs_eq)
  qed
qed

lemma roth_Gcd_remove_zero_int:
  fixes A :: "int set"
  shows "Gcd (A - {0}) = Gcd A"
proof (cases "0 \<in> A")
  case True
  have eq: "A = insert 0 (A - {0})" using True by auto
  have h0: "Gcd A = Gcd (insert 0 (A - {0}))"
    using eq by (rule arg_cong)
  have h1: "Gcd (insert 0 (A - {0})) = Gcd (A - {0})"
    by (simp only: Gcd_insert gcd_0_left normalize_Gcd)
  show ?thesis using h0 h1 by simp
next
  case False
  then show ?thesis by simp
qed

lemma roth_content_poly_to_mpoly:
  fixes Q :: "int poly"
  shows "Gcd (MPoly_Type.coeffs (poly_to_mpoly v Q)) =
    Polynomial.content Q"
  by (simp add: roth_coeffs_poly_to_mpoly
    roth_Gcd_remove_zero_int Polynomial.content_def)

lemma roth_primitive_poly_to_mpoly:
  fixes Q :: "int poly"
  shows "MPoly_Type.primitive (poly_to_mpoly v Q) \<longleftrightarrow>
    Polynomial.content Q = 1"
  by (simp add: MPoly_Type.primitive_def
    roth_content_poly_to_mpoly)

lemma roth_coeffs_mpoly_to_poly:
  fixes U :: "int mpoly"
  assumes uv: "vars U \<subseteq> {v}"
  shows "set (Polynomial.coeffs (mpoly_to_poly v U)) - {0} =
    MPoly_Type.coeffs U"
  using roth_coeffs_poly_to_mpoly[of v "mpoly_to_poly v U"]
    mpoly_to_poly_inverse[OF uv] by simp

lemma roth_content_mpoly_to_poly:
  fixes U :: "int mpoly"
  assumes uv: "vars U \<subseteq> {v}"
  shows "Polynomial.content (mpoly_to_poly v U) =
    Gcd (MPoly_Type.coeffs U)"
  using roth_content_poly_to_mpoly[of v "mpoly_to_poly v U"]
    mpoly_to_poly_inverse[OF uv] by simp

lemma roth_primitive_mpoly_to_poly:
  fixes U :: "int mpoly"
  assumes uv: "vars U \<subseteq> {v}"
  shows "Polynomial.content (mpoly_to_poly v U) = 1
    \<longleftrightarrow> MPoly_Type.primitive U"
  by (simp add: roth_content_mpoly_to_poly[OF uv]
    MPoly_Type.primitive_def)

lemma roth_int_coeff_sup_poly_coeff:
  fixes Q :: "int poly"
  shows "nat (abs (Polynomial.coeff Q k)) \<le>
    roth_int_coeff_sup (poly_to_mpoly v Q)"
  using roth_int_coeff_sup_coeff
    [of "poly_to_mpoly v Q" "Poly_Mapping.single v k"]
  by (simp add: coeff_poly_to_mpoly)

lemma roth_int_coeff_sup_poly_coeffs:
  fixes Q :: "int poly"
  assumes c: "c \<in> set (Polynomial.coeffs Q)"
  shows "nat (abs c) \<le> roth_int_coeff_sup (poly_to_mpoly v Q)"
proof -
  obtain k where "c = Polynomial.coeff Q k"
    using c range_coeff[of Q] by auto
  then show ?thesis
    using roth_int_coeff_sup_poly_coeff[of Q k v] by simp
qed

lemma roth_poly_to_mpoly_nonzero:
  fixes Q :: "'a::comm_ring_1 poly"
  assumes "Q \<noteq> 0"
  shows "poly_to_mpoly v Q \<noteq> 0"
  using assms poly_to_mpoly_inverse[of v Q]
    poly_to_mpoly_inverse[of v 0] poly_to_mpoly0[of v]
  by metis

lemma roth_mpoly_to_poly_nonzero:
  fixes U :: "'a::comm_ring_1 mpoly"
  assumes u: "U \<noteq> 0" and uv: "vars U \<subseteq> {v}"
  shows "mpoly_to_poly v U \<noteq> 0"
  using u mpoly_to_poly_inverse[OF uv] poly_to_mpoly0
  by metis

lemma roth_proj_height_poly_to_mpoly:
  fixes Q :: "int poly"
  assumes q: "Q \<noteq> 0" and prim: "Polynomial.content Q = 1"
  shows "roth_proj_height
    (replace_coeff of_int (poly_to_mpoly v Q) :: rat mpoly) =
    roth_int_coeff_sup (poly_to_mpoly v Q)"
  by (rule roth_proj_height_cast_primitive
    [OF roth_poly_to_mpoly_nonzero[OF q]])
    (simp add: roth_primitive_poly_to_mpoly prim)

section \<open>Mahler measure of a rational point\<close>

lemma roth_linear_cast_complex:
  fixes p q :: int
  assumes q: "q \<noteq> 0"
  shows "(map_poly of_int [:-p,q:] :: complex poly) =
    smult (of_int q) [:- (of_int p / of_int q), 1:]"
  using q by (simp add: smult_pCons)

lemma roth_mahler_smult_linear:
  fixes c a :: complex
  shows "mahler_measure_poly (smult c [:-a,1:]) =
    cmod c * max 1 (cmod a)"
  using mahler_measure_poly_explicit[of c "[a]"] by simp

lemma roth_mahler_linear_pre:
  fixes p q :: int
  assumes q: "q \<noteq> 0"
  shows "mahler_measure [:-p,q:] =
    of_int (abs q) * max 1 (of_int (abs p) / of_int (abs q))"
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
  shows "mahler_measure [:-p,q:] = of_int (max (abs p) q)"
  using roth_mahler_linear_pre[of q p] q
  by (simp add: max_mult_distrib_left)

lemma roth_mahler_mult:
  fixes Q R :: "int poly"
  shows "mahler_measure (Q*R) =
    mahler_measure Q * mahler_measure R"
  unfolding mahler_measure_def of_int_poly_hom.hom_mult
  by (rule measure_eq_prod)

lemma roth_mahler_one:
  "mahler_measure (1::int poly) = 1"
  by (simp add: mahler_measure_def mahler_measure_poly_def)

lemma roth_mahler_power:
  fixes Q :: "int poly"
  shows "mahler_measure (Q^n) = mahler_measure Q ^n"
  by (induction n)
    (simp_all add: roth_mahler_one roth_mahler_mult)

lemma roth_linear_content:
  fixes p q :: int
  assumes cpq: "coprime p q"
  shows "Polynomial.content [:-p,q:] = 1"
  using cpq by (simp add: coprime_commute)

lemma roth_linear_cast_rat:
  fixes p q :: int
  assumes q: "q \<noteq> 0"
  shows "(map_poly of_int [:-p,q:] :: rat poly) =
    smult (of_int q) [:- Rat.Fract p q, 1:]"
  using q by (simp add: smult_pCons Rat.Fract_of_int_quotient)

lemma roth_linear_power_content:
  fixes p q :: int
  assumes cpq: "coprime p q"
  shows "Polynomial.content ([:-p,q:] ^ n) = 1"
  by (induction n)
    (simp_all only: power_0 power_Suc content_1 content_mult
      roth_linear_content[OF cpq] mult_1_left mult_1_right)

lemma roth_linear_power_cast_rat:
  fixes p q :: int
  assumes q: "q \<noteq> 0"
  shows "(map_poly of_int ([:-p,q:] ^ n) :: rat poly) =
    smult ((of_int q)^n) ([:- Rat.Fract p q,1:]^n)"
  unfolding of_int_poly_hom.hom_power
    roth_linear_cast_rat[OF q] smult_power by simp

lemma roth_int_poly_cast_nonzero:
  fixes Q :: "int poly"
  assumes "Q \<noteq> 0"
  shows "(map_poly of_int Q :: rat poly) \<noteq> 0"
  using assms by simp

lemma roth_linear_power_cast_dvd:
  fixes Q :: "int poly"
  assumes q: "q \<noteq> (0::int)"
  shows "((map_poly of_int ([:-p,q:] ^ n) :: rat poly)
      dvd map_poly of_int Q) =
    ([:-Rat.Fract p q,1:] ^ n dvd map_poly of_int Q)"
  unfolding roth_linear_power_cast_rat[OF q]
  using q by (simp add: smult_dvd_iff)

lemma roth_linear_power_dvd:
  fixes Q :: "int poly"
  assumes q: "q \<noteq> (0::int)"
    and cpq: "coprime p q"
    and Q: "Q \<noteq> 0"
  shows "[:-p,q:] ^ n dvd Q \<longleftrightarrow>
    n \<le> Polynomial.order (Rat.Fract p q)
      (map_poly of_int Q :: rat poly)"
proof -
  have e1: "([:-p,q:] ^ n dvd Q) =
    ((map_poly of_int ([:-p,q:] ^ n) :: rat poly)
      dvd map_poly of_int Q)"
    by (rule dvd_poly_int_content_1
      [OF roth_linear_power_content[OF cpq]])
  have e2: "((map_poly of_int ([:-p,q:] ^ n) :: rat poly)
      dvd map_poly of_int Q) =
    ([:-Rat.Fract p q,1:] ^ n dvd map_poly of_int Q)"
    by (rule roth_linear_power_cast_dvd[OF q])
  have e3: "([:-Rat.Fract p q,1:] ^ n dvd
      (map_poly of_int Q :: rat poly)) =
    (n \<le> Polynomial.order (Rat.Fract p q)
      (map_poly of_int Q))"
    using order_divides[of "Rat.Fract p q" n
      "map_poly of_int Q"] roth_int_poly_cast_nonzero[OF Q]
    by blast
  show ?thesis using e1 e2 e3 by simp
qed

lemma roth_mahler_order_le:
  fixes Q :: "int poly"
  assumes q: "q > (0::int)"
    and cpq: "coprime p q"
    and Q: "Q \<noteq> 0"
  shows "of_int (max (abs p) q) ^
      Polynomial.order (Rat.Fract p q)
        (map_poly of_int Q :: rat poly)
    \<le> mahler_measure Q"
proof -
  let ?l = "Polynomial.order (Rat.Fract p q)
    (map_poly of_int Q :: rat poly)"
  have dvd: "[:-p,q:] ^ ?l dvd Q"
    using roth_linear_power_dvd[of q p Q ?l]
      q cpq Q by simp
  have "mahler_measure ([:-p,q:] ^ ?l) \<le> mahler_measure Q"
    by (rule mahler_measure_dvd[OF Q dvd])
  then show ?thesis
    by (simp add: roth_mahler_linear[OF q] roth_mahler_power)
qed

lemma roth_coprime_bridge:
  fixes p q :: int
  assumes cpq: "coprime p q"
  shows "algebraic_semidom_class.coprime p q"
  using cpq by (simp add: coprime_iff_gcd_eq_1)

lemma roth_rat_height_order_le:
  fixes Q :: "int poly"
  assumes q: "q > (0::int)"
    and cpq: "coprime p q"
    and Q: "Q \<noteq> 0"
  shows "real (roth_rat_height (Rat.Fract p q)) ^
      Polynomial.order (Rat.Fract p q)
        (map_poly of_int Q :: rat poly)
    \<le> mahler_measure Q"
  using roth_mahler_order_le[OF q cpq Q]
    roth_rat_height_Fract[OF q roth_coprime_bridge[OF cpq]] q
  by simp

lemma roth_coeff_square_le:
  fixes Q :: "int poly"
  assumes a: "a \<in> set (Polynomial.coeffs Q)"
  shows "a*a \<le>
    int (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2"
proof -
  have h: "abs a \<le>
    int (roth_int_coeff_sup (poly_to_mpoly v Q))"
    using roth_int_coeff_sup_poly_coeffs[OF a, of v] by simp
  have "(abs a)^2 \<le>
    int (roth_int_coeff_sup (poly_to_mpoly v Q))^2"
    by (rule power_mono[OF h]) simp
  then show ?thesis by (simp add: power2_eq_square)
qed

lemma roth_coeff_square_sum_le:
  fixes Q :: "int poly"
  shows "(\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a) \<le>
    int (length (Polynomial.coeffs Q)) *
      int (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2"
proof -
  have "(\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a) \<le>
    (\<Sum>a\<leftarrow>Polynomial.coeffs Q.
      int (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2)"
    by (rule sum_list_mono) (rule roth_coeff_square_le)
  also have "... =
    int (length (Polynomial.coeffs Q)) *
      int (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2"
    by (simp add: map_replicate_const sum_list_replicate)
  finally show ?thesis .
qed

lemma roth_cast_square_id:
  "real_of_int (int n * int H^2) = real n * (real H)^2"
  by simp

lemma roth_coeff_square_sum_real_le:
  fixes Q :: "int poly"
  shows "real_of_int
      (\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a) \<le>
    real (length (Polynomial.coeffs Q)) *
      real (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2"
proof -
  note h = roth_coeff_square_sum_le[of Q v]
  have hreal: "real_of_int
      (\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a) \<le>
    real_of_int (int (length (Polynomial.coeffs Q)) *
      int (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2)"
    by (subst of_int_le_iff) (rule h)
  show ?thesis using hreal
    by (simp only: roth_cast_square_id)
qed

lemma roth_mahler_coeff_sup_le:
  fixes Q :: "int poly"
  shows "mahler_measure Q \<le>
    sqrt (real (length (Polynomial.coeffs Q))) *
      real (roth_int_coeff_sup (poly_to_mpoly v Q))"
proof -
  have "mahler_measure Q \<le> sqrt (real_of_int
      (\<Sum>a\<leftarrow>Polynomial.coeffs Q. a*a))"
    by (rule Landau_inequality_mahler_measure)
  also have "... \<le> sqrt
      (real (length (Polynomial.coeffs Q)) *
        real (roth_int_coeff_sup (poly_to_mpoly v Q)) ^ 2)"
    by (rule real_sqrt_le_mono[OF roth_coeff_square_sum_real_le])
  also have "... = sqrt
      (real (length (Polynomial.coeffs Q))) *
        real (roth_int_coeff_sup (poly_to_mpoly v Q))"
    by (simp add: real_sqrt_mult)
  finally show ?thesis .
qed

lemma roth_sqrt_suc_le_exp:
  "sqrt (real (Suc n)) \<le> exp (real n)"
proof -
  have h: "sqrt (real (Suc n)) \<le> real (Suc n)"
    by (rule real_le_lsqrt)
      (simp_all add: power2_eq_square mult_le_cancel_left2)
  have e: "real (Suc n) \<le> exp (real n)"
    using exp_ge_add_one_self[of "real n"] by simp
  show ?thesis using h e by linarith
qed

lemma roth_mahler_exp_degree_le:
  fixes Q :: "int poly"
  assumes Q: "Q \<noteq> 0"
  shows "mahler_measure Q \<le>
    exp (real (degree Q)) *
      real (roth_int_coeff_sup (poly_to_mpoly v Q))"
  using roth_mahler_coeff_sup_le[of Q v]
    roth_sqrt_suc_le_exp[of "degree Q"] Q
  by (simp add: length_coeffs_degree;
    meson mult_right_mono of_nat_0_le_iff order_trans)

lemma roth_univariate_log_order_bound:
  fixes Q :: "int poly"
  assumes q: "q > (0::int)"
    and cpq: "coprime p q"
    and Q: "Q \<noteq> 0"
  shows "real (Polynomial.order (Rat.Fract p q)
      (map_poly of_int Q :: rat poly)) *
      roth_rat_log_height (Rat.Fract p q)
    \<le> ln (real (roth_int_coeff_sup (poly_to_mpoly v Q))) +
      real (degree Q)"
proof -
  let ?H = "real (roth_rat_height (Rat.Fract p q))"
  let ?C = "real (roth_int_coeff_sup (poly_to_mpoly v Q))"
  let ?l = "Polynomial.order (Rat.Fract p q)
    (map_poly of_int Q :: rat poly)"
  have b: "?H ^ ?l \<le> exp (real (degree Q)) * ?C"
    using roth_rat_height_order_le[OF q cpq Q]
      roth_mahler_exp_degree_le[OF Q]
    by (rule order_trans)
  have log: "ln (?H ^ ?l) \<le>
    ln (exp (real (degree Q)) * ?C)"
    using b by simp
  show ?thesis using log
    by (simp add: ln_realpow ln_mult_pos
      roth_rat_log_height_def mult.commute)
qed

lemma roth_primitive_poly_log_height:
  fixes Q :: "int poly"
  assumes q: "Q \<noteq> 0" and prim: "Polynomial.content Q = 1"
  shows "roth_proj_log_height
      (replace_coeff of_int (poly_to_mpoly v Q) :: rat mpoly) =
    ln (real (roth_int_coeff_sup (poly_to_mpoly v Q)))"
  unfolding roth_proj_log_height_def
  by (simp add: roth_proj_height_poly_to_mpoly[OF q prim])

section \<open>The bound for rational univariate polynomials\<close>

lemma roth_coprime_bridge_back:
  fixes p q :: int
  assumes cpq: "algebraic_semidom_class.coprime p q"
  shows "coprime p q"
  using cpq by (simp add: coprime_iff_gcd_eq_1)

lemma roth_rat_fraction_exists:
  fixes x :: rat
  shows "\<exists>p q::int. q > 0 \<and> coprime p q \<and>
    x = Rat.Fract p q"
proof -
  obtain p q where pq: "quotient_of x = (p,q)"
    by (cases "quotient_of x") auto
  have q: "q > 0" by (rule quotient_of_denom_pos[OF pq])
  have cpq: "coprime p q"
    using quotient_of_coprime[OF pq]
    by (rule roth_coprime_bridge_back)
  have x: "x = Rat.Fract p q"
    using Fract_quotient_of[of x] pq by simp
  show ?thesis using q cpq x by blast
qed

lemma roth_rat_poly_primitive_rep:
  fixes P :: "rat poly"
  assumes p: "P \<noteq> 0"
  shows "\<exists>Q::int poly. \<exists>c::rat.
    Q \<noteq> 0 \<and> Polynomial.content Q = 1 \<and> c \<noteq> 0 \<and>
    map_poly of_int Q = Polynomial.smult c P \<and>
    roth_proj_height (poly_to_mpoly v P) =
      roth_int_coeff_sup (poly_to_mpoly v Q)"
proof -
  have pmp: "poly_to_mpoly v P \<noteq> 0"
    by (rule roth_poly_to_mpoly_nonzero[OF p])
  obtain U::"int mpoly" where
    rep: "roth_integral_rep (poly_to_mpoly v P) U"
    and u: "U \<noteq> 0" and prim: "MPoly_Type.primitive U"
    using roth_primitive_rep_exists[OF pmp] by blast
  have uv: "vars U \<subseteq> {v}"
    using roth_vars_integral_rep[OF rep]
      roth_vars_poly_to_mpoly[of v P] by simp
  let ?Q = "mpoly_to_poly v U"
  have un: "poly_to_mpoly v ?Q = U"
    by (rule mpoly_to_poly_inverse[OF uv])
  have qnz: "?Q \<noteq> 0"
    by (rule roth_mpoly_to_poly_nonzero[OF u uv])
  have qprim: "Polynomial.content ?Q = 1"
    using roth_primitive_mpoly_to_poly[OF uv] prim by simp
  obtain c::rat where cnz: "c \<noteq> 0" and
    eq: "(replace_coeff of_int U :: rat mpoly) =
      MPoly_Type.smult c (poly_to_mpoly v P)"
    using rep by (auto simp: roth_integral_rep_def)
  have eqpoly: "map_poly of_int ?Q = Polynomial.smult c P"
    using arg_cong[OF eq, of "mpoly_to_poly v"]
    by (simp add: roth_mpoly_to_poly_cast
      roth_mpoly_to_poly_smult poly_to_mpoly_inverse)
  have height: "roth_proj_height (poly_to_mpoly v P) =
    roth_int_coeff_sup (poly_to_mpoly v ?Q)"
    using roth_proj_height_primitive_rep[OF pmp u prim rep] un by simp
  show ?thesis using qnz qprim cnz eqpoly height by blast
qed

lemma roth_univariate_rat_poly_log_order_bound:
  fixes P :: "rat poly"
  assumes P: "P \<noteq> 0"
  shows "real (Polynomial.order \<beta> P) * roth_rat_log_height \<beta> \<le>
    roth_proj_log_height (poly_to_mpoly v P) + real (degree P)"
proof -
  obtain p q::int where qpos: "q > 0" and cpq: "coprime p q"
    and beq: "\<beta> = Rat.Fract p q"
    using roth_rat_fraction_exists[of \<beta>] by blast
  obtain Q::"int poly" and c::rat where
    Qnz: "Q \<noteq> 0" and Qprim: "Polynomial.content Q = 1"
    and cnz: "c \<noteq> 0"
    and eq: "map_poly of_int Q = Polynomial.smult c P"
    and height: "roth_proj_height (poly_to_mpoly v P) =
      roth_int_coeff_sup (poly_to_mpoly v Q)"
    using roth_rat_poly_primitive_rep[OF P, of v] by blast
  have ord: "Polynomial.order \<beta> (map_poly of_int Q :: rat poly) =
    Polynomial.order \<beta> P"
    using eq cnz by (simp add: Polynomial.order_smult)
  have degcast: "degree (map_poly of_int Q :: rat poly) = degree Q"
    by (rule degree_map_poly) simp
  have deg: "degree Q = degree P"
    using degcast eq cnz by simp
  have h: "roth_proj_log_height (poly_to_mpoly v P) =
    ln (real (roth_int_coeff_sup (poly_to_mpoly v Q)))"
    using height by (simp add: roth_proj_log_height_def)
  note b = roth_univariate_log_order_bound[OF qpos cpq Qnz, of v]
  show ?thesis using b beq ord deg h by metis
qed

lemma roth_univariate_mpoly_log_order_bound:
  fixes P :: "rat mpoly"
  assumes P: "P \<noteq> 0" and pv: "vars P \<subseteq> {v}"
  shows "real (Polynomial.order \<beta> (mpoly_to_poly v P)) *
    roth_rat_log_height \<beta> \<le>
    roth_proj_log_height P + real (degree (mpoly_to_poly v P))"
proof -
  have pn: "mpoly_to_poly v P \<noteq> 0"
    by (rule roth_mpoly_to_poly_nonzero[OF P pv])
  have peq: "poly_to_mpoly v (mpoly_to_poly v P) = P"
    by (rule mpoly_to_poly_inverse[OF pv])
  show ?thesis
    using roth_univariate_rat_poly_log_order_bound[OF pn, of \<beta> v]
      peq by simp
qed

section \<open>Univariate order and the Roth index\<close>

lemma roth_translate_poly_to_mpoly:
  fixes p :: "rat poly"
  shows "roth_translate a (poly_to_mpoly v p) =
    poly_to_mpoly v (pcompose p [:a v,1:])"
proof -
  have vl: "vars (roth_translate a (poly_to_mpoly v p)) \<subseteq> {v}"
    using roth_vars_translate_subset roth_vars_poly_to_mpoly[of v p]
    by blast
  have aux: "insertion (\<lambda>_. x)
    (roth_translate a (poly_to_mpoly v p)) =
    insertion (\<lambda>u. x + a u) (poly_to_mpoly v p)" for x
    by (simp add: roth_translate_def roth_insertion_subst insertion_add)
  have aux2: "insertion (\<lambda>u. x + a u) (poly_to_mpoly v p) =
    insertion (\<lambda>_. x + a v) (poly_to_mpoly v p)" for x
    by (rule insertion_irrelevant_vars)
      (use roth_vars_poly_to_mpoly[of v p] in auto)
  have eval: "poly (mpoly_to_poly v
      (roth_translate a (poly_to_mpoly v p))) x =
    poly p (x + a v)" for x
    using aux[of x] aux2[of x]
      poly_eq_insertion[OF vl, of x]
      poly_eq_insertion[OF roth_vars_poly_to_mpoly[of v p],
        of "x + a v"]
      poly_to_mpoly_inverse[of v p]
    by metis
  have peq: "mpoly_to_poly v
      (roth_translate a (poly_to_mpoly v p)) =
    pcompose p [:a v,1:]"
    by (rule poly_ext) (simp add: eval poly_pcompose add.commute)
  show ?thesis using peq mpoly_to_poly_inverse[OF vl] by simp
qed

lemma roth_order_zero_coeff:
  fixes p :: "rat poly"
  assumes p: "p \<noteq> 0"
  shows "(\<forall>k<Polynomial.order 0 p. coeff p k = 0) \<and>
    coeff p (Polynomial.order 0 p) \<noteq> 0"
proof -
  let ?l = "Polynomial.order 0 p"
  have ld: "monom 1 ?l dvd p"
    using order_1[of 0 p] by (simp add: monom_altdef)
  have nd: "\<not> monom 1 (Suc ?l) dvd p"
    using order_2[OF p, of 0] by (simp add: monom_altdef)
  have low: "\<forall>k<?l. coeff p k = 0"
    using ld by (simp add: monom_1_dvd_iff')
  have high: "coeff p ?l \<noteq> 0"
    using low nd by (auto simp: monom_1_dvd_iff' dest: less_SucE)
  show ?thesis using low high by blast
qed

lemma roth_order_shift:
  fixes p :: "rat poly"
  assumes p: "p \<noteq> 0"
  shows "Polynomial.order 0 (pcompose p [:\<beta>,1:]) =
    Polynomial.order \<beta> p"
proof -
  obtain q where peq: "p = [:-\<beta>,1:] ^
      Polynomial.order \<beta> p * q"
    and qnd: "\<not> [:-\<beta>,1:] dvd q"
    using order_decomp[OF p, of \<beta>] by blast
  have q0: "poly q \<beta> \<noteq> 0"
    using qnd by (simp add: poly_eq_0_iff_dvd)
  have lin: "pcompose [:-\<beta>,1:] [:\<beta>,1:] = [:0,1:]"
    by (simp add: pcompose_pCons pcompose_1)
  have cpow: "pcompose ([:-\<beta>,1:] ^ n) [:\<beta>,1:] =
    [:0,1:] ^ n" for n
    by (induction n)
      (simp_all only: power_0 power_Suc pcompose_mult pcompose_1 lin)
  have mid: "pcompose (([:-\<beta>,1:] ^
      Polynomial.order \<beta> p) * q) [:\<beta>,1:] =
    monom 1 (Polynomial.order \<beta> p) *
      pcompose q [:\<beta>,1:]"
    by (simp only: pcompose_mult cpow monom_altdef smult_1_left)
  have shift: "pcompose p [:\<beta>,1:] =
    monom 1 (Polynomial.order \<beta> p) *
      pcompose q [:\<beta>,1:]"
    using mid peq by metis
  have qshift0: "coeff (pcompose q [:\<beta>,1:]) 0 \<noteq> 0"
    using q0 by simp
  have qshift: "pcompose q [:\<beta>,1:] \<noteq> 0"
    using qshift0 by (metis coeff_0)
  have qord: "Polynomial.order 0 (pcompose q [:\<beta>,1:]) = 0"
    by (rule order_0I) (simp add: poly_pcompose q0)
  have nz: "monom 1 (Polynomial.order \<beta> p) *
    pcompose q [:\<beta>,1:] \<noteq> 0"
    using qshift by simp
  show ?thesis using shift qord nz
    by (simp add: Polynomial.order_mult)
qed

lemma roth_univariate_taylor_coeff:
  fixes p :: "rat poly"
  shows "roth_taylor_coeff a (Poly_Mapping.single v k)
      (poly_to_mpoly v p) =
    Polynomial.coeff (pcompose p [:a v,1:]) k"
  by (simp add: roth_taylor_coeff_def
    roth_translate_poly_to_mpoly coeff_poly_to_mpoly)

lemma roth_univariate_taylor_support:
  fixes p :: "rat poly"
  assumes tc: "roth_taylor_coeff a I (poly_to_mpoly v p) \<noteq> 0"
  shows "I = Poly_Mapping.single v (Poly_Mapping.lookup I v)"
proof -
  have ik: "I \<in> Poly_Mapping.keys
    (mapping_of (roth_translate a (poly_to_mpoly v p)))"
    using tc by (simp add: roth_taylor_coeff_key)
  have vin: "Poly_Mapping.keys I \<subseteq>
    vars (roth_translate a (poly_to_mpoly v p))"
    using ik by (auto simp: vars_def)
  have kv: "Poly_Mapping.keys I \<subseteq> {v}"
    using vin roth_vars_translate_subset
      roth_vars_poly_to_mpoly[of v p] by blast
  have off: "Poly_Mapping.lookup I u = 0" if "u \<noteq> v" for u
    using kv that by (auto simp: in_keys_iff)
  show ?thesis using off
    by (metis Poly_Mapping.poly_mapping_eqI
      lookup_single_eq lookup_single_not_eq)
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
  have ord: "Polynomial.order 0 ?s = ?l"
    using roth_order_shift[OF p, of \<beta>] .
  have low: "\<forall>k<?l. Polynomial.coeff ?s k = 0"
    and high: "Polynomial.coeff ?s ?l \<noteq> 0"
    using roth_order_zero_coeff[OF snz] ord by auto
  have tcl: "roth_taylor_coeff (\<lambda>_. \<beta>)
      (Poly_Mapping.single 0 ?l) (poly_to_mpoly 0 p) \<noteq> 0"
    using high by (simp add: roth_univariate_taylor_coeff)
  have w: "roth_weight 1 r (Poly_Mapping.single 0 ?l) =
    real ?l / real (r 0)"
    by (simp add: roth_weight_def)
  have ub: "roth_index 1 r (\<lambda>_. \<beta>)
      (poly_to_mpoly 0 p) \<le> ereal (real ?l / real (r 0))"
    using roth_index_le_coeff[OF tcl, of 1 r] w by metis
  have pmp: "poly_to_mpoly 0 p \<noteq> 0"
    by (rule roth_poly_to_mpoly_nonzero[OF p])
  obtain I where
    tc: "roth_taylor_coeff (\<lambda>_. \<beta>) I
      (poly_to_mpoly 0 p) \<noteq> 0"
    and ieq: "roth_index 1 r (\<lambda>_. \<beta>)
      (poly_to_mpoly 0 p) = ereal (roth_weight 1 r I)"
    using roth_index_attained[OF pmp, where m=1 and r=r
      and a="\<lambda>_. \<beta>"] by blast
  have irep: "I = Poly_Mapping.single 0 (Poly_Mapping.lookup I 0)"
    by (rule roth_univariate_taylor_support[OF tc])
  have kcoeff: "Polynomial.coeff ?s (Poly_Mapping.lookup I 0)
      \<noteq> 0"
    using tc irep roth_univariate_taylor_coeff by metis
  have lk: "?l \<le> Poly_Mapping.lookup I 0"
    using low kcoeff by (metis not_le_imp_less)
  have wI: "roth_weight 1 r I =
    real (Poly_Mapping.lookup I 0) / real (r 0)"
    by (simp add: roth_weight_def)
  have lb: "ereal (real ?l / real (r 0)) \<le>
      roth_index 1 r (\<lambda>_. \<beta>) (poly_to_mpoly 0 p)"
    using ieq wI lk r by (simp add: divide_right_mono)
  show ?thesis by (rule antisym[OF ub lb])
qed

lemma roth_univariate_index_bound:
  fixes p :: "rat poly" and r :: "nat \<Rightarrow> nat"
  assumes p: "p \<noteq> 0" and r: "r 0 > 0"
    and deg: "degree p \<le> r 0" and eta: "\<eta> > 0"
    and h: "roth_proj_log_height (poly_to_mpoly 0 p) +
      real (r 0) \<le> \<eta> * real (r 0) *
        roth_rat_log_height \<beta>"
  shows "roth_index 1 r (\<lambda>_. \<beta>)
    (poly_to_mpoly 0 p) \<le> ereal \<eta>"
proof -
  have rpos: "(0::real) < real (r 0)"
    using r by simp
  have posprod: "0 < \<eta> * real (r 0) *
      roth_rat_log_height \<beta>"
    using h rpos
      roth_proj_log_height_nonneg[of "poly_to_mpoly 0 p"]
    by linarith
  have ep: "0 < \<eta> * real (r 0)"
    using eta rpos by simp
  have hp: "0 < roth_rat_log_height \<beta>"
    using posprod ep by (auto simp: zero_less_mult_iff)
  have b: "real (Polynomial.order \<beta> p) *
      roth_rat_log_height \<beta> \<le>
    roth_proj_log_height (poly_to_mpoly 0 p) +
      real (degree p)"
    by (rule roth_univariate_rat_poly_log_order_bound[OF p])
  have bd: "real (Polynomial.order \<beta> p) *
      roth_rat_log_height \<beta> \<le>
    \<eta> * real (r 0) * roth_rat_log_height \<beta>"
    using b deg h by linarith
  have l: "real (Polynomial.order \<beta> p) \<le>
      \<eta> * real (r 0)"
    using bd hp by (simp add: mult_le_cancel_right_pos)
  have ratio: "real (Polynomial.order \<beta> p) /
      real (r 0) \<le> \<eta>"
    using l rpos by (simp add: pos_divide_le_eq)
  show ?thesis
    using roth_univariate_index_order
      [where p=p and r=r and \<beta>=\<beta>] p r ratio by simp
qed

lemma roth_univariate_mpoly_index_bound:
  fixes P :: "rat mpoly" and r :: "nat \<Rightarrow> nat"
  assumes P: "P \<noteq> 0" and pv: "vars P \<subseteq> {0}"
    and r: "r 0 > 0"
    and deg: "degree (mpoly_to_poly 0 P) \<le> r 0"
    and eta: "\<eta> > 0"
    and h: "roth_proj_log_height P +
      real (r 0) \<le> \<eta> * real (r 0) *
        roth_rat_log_height \<beta>"
  shows "roth_index 1 r (\<lambda>_. \<beta>) P \<le> ereal \<eta>"
proof -
  have pn: "mpoly_to_poly 0 P \<noteq> 0"
    by (rule roth_mpoly_to_poly_nonzero[OF P pv])
  have peq: "poly_to_mpoly 0 (mpoly_to_poly 0 P) = P"
    by (rule mpoly_to_poly_inverse[OF pv])
  show ?thesis
    using roth_univariate_index_bound
      [where p="mpoly_to_poly 0 P" and r=r
        and \<eta>=\<eta> and \<beta>=\<beta>] pn r deg eta h peq by simp
qed

lemma roth_univariate_vars_of_box:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box 1 r P"
  shows "vars P \<subseteq> {0}"
  using box by (auto simp: vars_def roth_poly_in_box_def
    dest: roth_exponent_boxD(1))

lemma roth_univariate_degree_of_box:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box 1 r P"
  shows "degree (mpoly_to_poly 0 P) \<le> r 0"
proof (rule degree_le, intro allI impI)
  fix i assume i: "r 0 < i"
  have outside: "Poly_Mapping.single 0 i \<notin>
      roth_exponent_box 1 r"
    using i by (simp add: roth_exponent_box_iff)
  show "Polynomial.coeff (mpoly_to_poly 0 P) i = 0"
    using roth_coeff_zero_outside_box[OF box outside] by simp
qed

theorem roth_lemma_one_variable:
  fixes P :: "rat mpoly" and r :: "nat \<Rightarrow> nat"
  assumes P: "P \<noteq> 0" and box: "roth_poly_in_box 1 r P"
    and r: "r 0 > 0" and eta: "\<eta> > 0"
    and h: "roth_proj_log_height P +
      real (r 0) \<le> \<eta> * real (r 0) *
        roth_rat_log_height \<beta>"
  shows "roth_index 1 r (\<lambda>_. \<beta>) P \<le> ereal \<eta>"
  using roth_univariate_mpoly_index_bound
      [where P=P and r=r and \<eta>=\<eta> and \<beta>=\<beta>]
    P box r eta h
    roth_univariate_vars_of_box[OF box]
    roth_univariate_degree_of_box[OF box]
  by blast

end
