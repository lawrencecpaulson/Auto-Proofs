theory Roth_Univariate_Index
  imports Roth_Univariate_Rational
begin

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
