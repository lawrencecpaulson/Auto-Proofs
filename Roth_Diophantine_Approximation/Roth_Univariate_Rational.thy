theory Roth_Univariate_Rational
  imports Roth_Univariate_Order
begin

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

end
