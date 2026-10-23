theory Roth_Approximation
  imports
    "HOL-Computational_Algebra.Polynomial"
    "HOL-Library.Infinite_Set"
begin

section \<open>Rational approximants to a real number\<close>

definition roth_good_pairs :: "real \<Rightarrow> real \<Rightarrow> (int \<times> int) set" where
  "roth_good_pairs \<alpha> \<kappa> =
    {(p,q). q > 0 \<and> coprime p q \<and>
      \<bar>\<alpha> - of_int p / of_int q\<bar> < 1 / of_int q powr \<kappa>}"

lemma roth_good_pairs_iff [simp]:
  "(p,q) \<in> roth_good_pairs \<alpha> \<kappa> \<longleftrightarrow>
    q > 0 \<and> coprime p q \<and>
      \<bar>\<alpha> - of_int p / of_int q\<bar> < 1 / of_int q powr \<kappa>"
  by (simp add: roth_good_pairs_def)

definition roth_good_nat_pairs :: "real \<Rightarrow> real \<Rightarrow> (int \<times> nat) set" where
  "roth_good_nat_pairs \<alpha> \<kappa> =
    {(p,q). q > 0 \<and> coprime p (int q) \<and>
      \<bar>\<alpha> - of_int p / of_nat q\<bar> < 1 / of_nat q powr \<kappa>}"

lemma roth_good_pairs_image_nat:
  "roth_good_pairs \<alpha> \<kappa> =
    (\<lambda>(p,q). (p,int q)) ` roth_good_nat_pairs \<alpha> \<kappa>"
proof
  show "roth_good_pairs \<alpha> \<kappa> \<subseteq>
      (\<lambda>(p,q). (p,int q)) ` roth_good_nat_pairs \<alpha> \<kappa>"
  proof
    fix pq
    assume "pq \<in> roth_good_pairs \<alpha> \<kappa>"
    then obtain p q where pq: "pq = (p,q)" and q: "q > 0"
      and cop: "coprime p q"
      and near: "\<bar>\<alpha> - of_int p / of_int q\<bar> < 1 / of_int q powr \<kappa>"
      by (cases pq) auto
    have "(p,nat q) \<in> roth_good_nat_pairs \<alpha> \<kappa>"
      using q cop near by (simp add: roth_good_nat_pairs_def)
    then show "pq \<in> (\<lambda>(p,q). (p,int q)) ` roth_good_nat_pairs \<alpha> \<kappa>"
      using pq q by force
  qed
next
  show "(\<lambda>(p,q). (p,int q)) ` roth_good_nat_pairs \<alpha> \<kappa> \<subseteq>
      roth_good_pairs \<alpha> \<kappa>"
    by (auto simp: roth_good_nat_pairs_def)
qed

lemma finite_roth_good_nat_pairs_iff:
  "finite (roth_good_nat_pairs \<alpha> \<kappa>) \<longleftrightarrow>
    finite (roth_good_pairs \<alpha> \<kappa>)"
proof -
  have "inj_on (\<lambda>(p,q). (p,int q)) (roth_good_nat_pairs \<alpha> \<kappa>)"
    by (auto intro: inj_onI)
  then show ?thesis
    by (simp add: roth_good_pairs_image_nat finite_image_iff)
qed

lemma rational_approximant_height_bound:
  fixes \<alpha> E :: real and p q :: int
  assumes q: "q > 0"
    and near: "\<bar>\<alpha> - of_int p / of_int q\<bar> < E"
  shows "\<bar>p\<bar> \<le> \<lceil>of_int q * (\<bar>\<alpha>\<bar> + E)\<rceil>"
proof -
  have q0: "(of_int q :: real) \<noteq> 0"
    using q by simp
  have q_real: "(0::real) < of_int q"
    using q by simp
  have pd: "\<bar>of_int p / of_int q\<bar> \<le>
      \<bar>\<alpha>\<bar> + \<bar>\<alpha> - of_int p / of_int q\<bar>"
    by linarith
  have pd_lt: "\<bar>of_int p / of_int q\<bar> < \<bar>\<alpha>\<bar> + E"
    using pd near by linarith
  have "(of_int (\<bar>p\<bar>) :: real) =
      \<bar>of_int q * (of_int p / of_int q)\<bar>"
    using q0 by (simp add: abs_mult)
  also have "\<dots> = of_int q * \<bar>of_int p / of_int q\<bar>"
    using q by (simp add: abs_mult)
  also have "\<dots> < of_int q * (\<bar>\<alpha>\<bar> + E)"
    using pd_lt q_real by (rule mult_strict_left_mono)
  also have "\<dots> \<le> of_int \<lceil>of_int q * (\<bar>\<alpha>\<bar> + E)\<rceil>"
    by (rule le_of_int_ceiling)
  finally show ?thesis
    by simp
qed

lemma finite_roth_numerators:
  fixes \<alpha> \<kappa> :: real and q :: int
  assumes q: "q > 0"
  shows "finite {p::int. \<bar>\<alpha> - of_int p / of_int q\<bar> <
    1 / of_int q powr \<kappa>}"
proof -
  let ?E = "1 / of_int q powr \<kappa>"
  let ?S = "{p::int. \<bar>\<alpha> - of_int p / of_int q\<bar> < ?E}"
  let ?B = "\<lceil>of_int q * (\<bar>\<alpha>\<bar> + ?E)\<rceil>"
  have p_bound: "\<bar>p\<bar> \<le> ?B" if p: "p \<in> ?S" for p
    using rational_approximant_height_bound[OF q] p by simp
  have "abs ` ?S \<subseteq> {..?B}"
    using p_bound by auto
  then show ?thesis
    by (auto simp: finite_int_iff_bounded_le)
qed

lemma finite_roth_good_pairs_bounded_denominator:
  fixes B :: int
  shows "finite {(p,q) \<in> roth_good_pairs \<alpha> \<kappa>. q \<le> B}"
proof -
  let ?Q = "{1..B}"
  let ?F = "\<lambda>q. {p. (p,q) \<in> roth_good_pairs \<alpha> \<kappa>}"
  have finF: "finite (?F q)" if q: "q \<in> ?Q" for q
  proof -
    have qpos: "q > 0"
      using q by simp
    have "?F q \<subseteq> {p::int. \<bar>\<alpha> - of_int p / of_int q\<bar> <
      1 / of_int q powr \<kappa>}"
      by auto
    then show ?thesis
      using finite_roth_numerators[OF qpos] by (rule finite_subset)
  qed
  have finU: "finite (\<Union>q\<in>?Q. (\<lambda>p. (p,q)) ` ?F q)"
    using finF by simp
  have sub: "{(p,q) \<in> roth_good_pairs \<alpha> \<kappa>. q \<le> B} \<subseteq>
      (\<Union>q\<in>?Q. (\<lambda>p. (p,q)) ` ?F q)"
  proof
    fix z
    assume z: "z \<in> {(p,q) \<in> roth_good_pairs \<alpha> \<kappa>. q \<le> B}"
    obtain p q where z_def: "z = (p,q)"
      by (cases z) auto
    have qQ: "q \<in> ?Q"
      using z z_def by auto
    have pF: "p \<in> ?F q"
      using z z_def by auto
    show "z \<in> (\<Union>q\<in>?Q. (\<lambda>p. (p,q)) ` ?F q)"
      using qQ pF z_def by blast
  qed
  show ?thesis
    using sub finU by (rule finite_subset)
qed

lemma finite_roth_good_pairs_iff_bounded_denominator:
  "finite (roth_good_pairs \<alpha> \<kappa>) \<longleftrightarrow>
    (\<exists>B::int. \<forall>pq\<in>roth_good_pairs \<alpha> \<kappa>. snd pq \<le> B)"
proof
  assume fin: "finite (roth_good_pairs \<alpha> \<kappa>)"
  then have "finite (snd ` roth_good_pairs \<alpha> \<kappa>)"
    by simp
  then obtain B :: int where B:
      "abs ` (snd ` roth_good_pairs \<alpha> \<kappa>) \<subseteq> {..B}"
    using finite_int_iff_bounded_le by blast
  show "\<exists>B::int. \<forall>pq\<in>roth_good_pairs \<alpha> \<kappa>. snd pq \<le> B"
    using B by fastforce
next
  assume "\<exists>B::int. \<forall>pq\<in>roth_good_pairs \<alpha> \<kappa>. snd pq \<le> B"
  then obtain B :: int where B:
      "\<forall>pq\<in>roth_good_pairs \<alpha> \<kappa>. snd pq \<le> B"
    by blast
  have "roth_good_pairs \<alpha> \<kappa> =
      {(p,q) \<in> roth_good_pairs \<alpha> \<kappa>. q \<le> B}"
    using B by auto
  then show "finite (roth_good_pairs \<alpha> \<kappa>)"
    using finite_roth_good_pairs_bounded_denominator by simp
qed

corollary infinite_roth_good_pairs_iff_unbounded_denominator:
  "infinite (roth_good_pairs \<alpha> \<kappa>) \<longleftrightarrow>
    (\<forall>B::int. \<exists>pq\<in>roth_good_pairs \<alpha> \<kappa>. B < snd pq)"
  using finite_roth_good_pairs_iff_bounded_denominator
  by (auto simp: not_le)

lemma roth_finite_exponent_iff:
  "(\<forall>\<alpha> \<kappa>. algebraic \<alpha> \<and> \<alpha> \<notin> \<rat> \<and>
      infinite (roth_good_pairs \<alpha> \<kappa>) \<longrightarrow> \<kappa> \<le> 2) \<longleftrightarrow>
    (\<forall>\<alpha> \<delta>. algebraic \<alpha> \<and> \<alpha> \<notin> \<rat> \<and> \<delta> > 0 \<longrightarrow>
      finite (roth_good_pairs \<alpha> (2 + \<delta>)))"
proof
  assume h: "\<forall>\<alpha> \<kappa>. algebraic \<alpha> \<and> \<alpha> \<notin> \<rat> \<and>
    infinite (roth_good_pairs \<alpha> \<kappa>) \<longrightarrow> \<kappa> \<le> 2"
  show "\<forall>\<alpha> \<delta>. algebraic \<alpha> \<and> \<alpha> \<notin> \<rat> \<and> \<delta> > 0 \<longrightarrow>
    finite (roth_good_pairs \<alpha> (2 + \<delta>))"
  proof (intro allI impI)
    fix \<alpha> \<delta> :: real
    assume a: "algebraic \<alpha> \<and> \<alpha> \<notin> \<rat> \<and> \<delta> > 0"
    show "finite (roth_good_pairs \<alpha> (2 + \<delta>))"
    proof (rule ccontr)
      assume "\<not> finite (roth_good_pairs \<alpha> (2 + \<delta>))"
      then have "2 + \<delta> \<le> 2"
        using h a by blast
      then show False
        using a by linarith
    qed
  qed
next
  assume h: "\<forall>\<alpha> \<delta>. algebraic \<alpha> \<and> \<alpha> \<notin> \<rat> \<and> \<delta> > 0 \<longrightarrow>
    finite (roth_good_pairs \<alpha> (2 + \<delta>))"
  show "\<forall>\<alpha> \<kappa>. algebraic \<alpha> \<and> \<alpha> \<notin> \<rat> \<and>
    infinite (roth_good_pairs \<alpha> \<kappa>) \<longrightarrow> \<kappa> \<le> 2"
  proof (intro allI impI)
    fix \<alpha> \<kappa> :: real
    assume a: "algebraic \<alpha> \<and> \<alpha> \<notin> \<rat> \<and>
      infinite (roth_good_pairs \<alpha> \<kappa>)"
    show "\<kappa> \<le> 2"
    proof (rule ccontr)
      assume "\<not> \<kappa> \<le> 2"
      then have pos: "\<kappa> - 2 > 0"
        by linarith
      have "finite (roth_good_pairs \<alpha> (2 + (\<kappa> - 2)))"
        using h a pos by blast
      then show False
        using a by simp
    qed
  qed
qed

section \<open>Scaling reduced approximants\<close>

lemma roth_scaled_gcd:
  fixes c p q :: int
  assumes "coprime p q"
  shows "gcd (c * p) q = gcd c q"
  using assms by (simp add: gcd_mult_left_right_cancel coprime_commute)

lemma roth_scaled_denominator:
  fixes c p q :: int
  assumes c: "c > 0" and q: "q > 0" and cop: "coprime p q"
  defines "g \<equiv> gcd (c * p) q"
  shows "g > 0" "g dvd c" "g dvd q"
    "q div g > 0" "q div g \<le> q" "q \<le> c * (q div g)"
proof -
  have g_eq: "g = gcd c q"
    using cop by (simp add: g_def roth_scaled_gcd)
  have gpos: "g > 0"
    using q by (simp add: g_eq)
  have gc: "g dvd c"
    by (simp add: g_eq)
  have gq: "g dvd q"
    by (simp add: g_eq)
  have glec: "g \<le> c"
    using c by (simp add: g_eq)
  have gleq: "g \<le> q"
    using q by (simp add: g_eq)
  have qdiv: "q div g > 0"
    using q gpos gleq by (simp add: pos_imp_zdiv_pos_iff)
  have qeq: "g * (q div g) = q"
    using gq by (simp add: dvd_div_mult_self)
  show "g > 0" "g dvd c" "g dvd q" "q div g > 0"
    using gpos gc gq qdiv by auto
  have "(1::int) * (q div g) \<le> g * (q div g)"
    using gpos qdiv by (intro mult_right_mono) auto
  show "q div g \<le> q"
    using \<open>(1::int) * (q div g) \<le> g * (q div g)\<close> qeq by simp
  have "g * (q div g) \<le> c * (q div g)"
    using glec qdiv by (intro mult_right_mono) auto
  show "q \<le> c * (q div g)"
    using \<open>g * (q div g) \<le> c * (q div g)\<close> qeq by simp
qed

definition roth_scaled_pair :: "int \<Rightarrow> (int \<times> int) \<Rightarrow> (int \<times> int)" where
  "roth_scaled_pair c pq = Rat.normalize (c * fst pq, snd pq)"

lemma roth_scaled_pair_properties:
  fixes c p q :: int
  assumes c: "c > 0" and q: "q > 0" and cop: "coprime p q"
  defines "pq' \<equiv> roth_scaled_pair c (p,q)"
  shows "snd pq' > 0" "coprime (fst pq') (snd pq')"
    "snd pq' \<le> q" "q \<le> c * snd pq'"
    "(of_int (fst pq') :: real) / of_int (snd pq') =
      of_int c * (of_int p / of_int q)"
proof -
  let ?g = "gcd (c * p) q"
  have norm: "pq' = (c * p div ?g, q div ?g)"
    using q by (simp add: pq'_def roth_scaled_pair_def Rat.normalize_def Let_def)
  have q'pos: "snd pq' > 0"
    using norm roth_scaled_denominator(4)[OF c q cop] by simp
  show "snd pq' > 0"
    by (rule q'pos)
  show "coprime (fst pq') (snd pq')"
    using norm q by (simp add: div_gcd_coprime)
  show "snd pq' \<le> q" "q \<le> c * snd pq'"
    using roth_scaled_denominator[OF c q cop] norm by simp_all
  have r: "Fract (fst pq') (snd pq') = Fract (c * p) q"
    using Rat.normalize_eq by (simp add: pq'_def roth_scaled_pair_def)
  have "(of_int (fst pq') :: real) / of_int (snd pq') =
      of_rat (Fract (fst pq') (snd pq'))"
    using q'pos by (simp add: of_rat_rat)
  also have "\<dots> = of_rat (Fract (c * p) q)"
    using r by simp
  also have "\<dots> = of_int c * (of_int p / of_int q)"
    using q by (simp add: of_rat_rat)
  finally show "(of_int (fst pq') :: real) / of_int (snd pq') =
    of_int c * (of_int p / of_int q)" .
qed

lemma roth_powr_threshold:
  fixes c \<eta> :: real
  assumes c: "c > 0" and eta: "\<eta> > 0"
  obtains B :: int where "B > 0"
    "\<And>q::int. q \<ge> B \<Longrightarrow> c < of_int q powr \<eta>"
proof -
  obtain B :: int where B: "max 1 (c powr (1 / \<eta>)) < of_int B"
    using ex_less_of_int by blast
  have Bpos: "B > 0"
    using B by simp
  have cpow: "(c powr (1 / \<eta>)) powr \<eta> = c"
    using c eta by (simp add: powr_powr)
  have bound: "c < of_int q powr \<eta>" if "q \<ge> B" for q :: int
  proof -
    have "c powr (1 / \<eta>) < of_int q"
      using B that by simp
    then have "(c powr (1 / \<eta>)) powr \<eta> < of_int q powr \<eta>"
      using eta c by (intro powr_less_mono2) auto
    then show ?thesis
      using cpow by simp
  qed
  show thesis
    by (rule that[OF Bpos bound])
qed

lemma roth_scaled_good_pair:
  fixes c p q :: int and \<alpha> \<epsilon> \<delta> :: real
  assumes c: "c > 0" and eps: "\<epsilon> > \<delta>" and delta: "\<delta> > 0"
    and good: "(p,q) \<in> roth_good_pairs \<alpha> (2 + \<epsilon>)"
    and large: "of_int c < of_int q powr (\<epsilon> - \<delta>)"
  shows "roth_scaled_pair c (p,q) \<in>
    roth_good_pairs (of_int c * \<alpha>) (2 + \<delta>)"
proof -
  let ?pq' = "roth_scaled_pair c (p,q)"
  have q: "q > 0" and cop: "coprime p q"
    and near: "\<bar>\<alpha> - of_int p / of_int q\<bar> <
      1 / of_int q powr (2 + \<epsilon>)"
    using good by auto
  have q'pos: "snd ?pq' > 0"
    using roth_scaled_pair_properties(1)[OF c q cop] by simp
  have cop': "coprime (fst ?pq') (snd ?pq')"
    using roth_scaled_pair_properties(2)[OF c q cop] by simp
  have q'le: "snd ?pq' \<le> q"
    using roth_scaled_pair_properties(3)[OF c q cop] by simp
  have frac: "(of_int (fst ?pq') :: real) / of_int (snd ?pq') =
    of_int c * (of_int p / of_int q)"
    using roth_scaled_pair_properties(5)[OF c q cop] by simp
  have qreal: "(0::real) < of_int q"
    using q by simp
  have creal: "(0::real) < of_int c"
    using c by simp
  have q'real: "(0::real) < of_int (snd ?pq')"
    using q'pos by simp
  have eta: "\<epsilon> - \<delta> > 0"
    using eps by simp
  have r: "2 + \<delta> > 0"
    using delta by simp
  have qpow: "0 < of_int q powr (2 + \<epsilon>)"
    using qreal by simp
  have pow_eq: "of_int q powr (2 + \<epsilon>) =
    of_int q powr (2 + \<delta>) * of_int q powr (\<epsilon> - \<delta>)"
    by (subst powr_add[symmetric]) simp
  have qrpos: "0 < of_int q powr (2 + \<delta>)"
    using qreal by simp
  have mult_bound: "of_int c * of_int q powr (2 + \<delta>) <
    of_int q powr (2 + \<epsilon>)"
  proof -
    have "of_int q powr (2 + \<delta>) * of_int c <
      of_int q powr (2 + \<delta>) * of_int q powr (\<epsilon> - \<delta>)"
      using large qrpos by (rule mult_strict_left_mono)
    then show ?thesis
      by (simp add: pow_eq mult.commute)
  qed
  have bound: "of_int c / of_int q powr (2 + \<epsilon>) <
    1 / of_int q powr (2 + \<delta>)"
    using mult_bound qpow qrpos by (simp add: field_simps)
  have pow_le: "of_int (snd ?pq') powr (2 + \<delta>) \<le>
    of_int q powr (2 + \<delta>)"
    using r q'real q'le by (intro powr_mono2) auto
  have inv_le: "1 / of_int q powr (2 + \<delta>) \<le>
    1 / of_int (snd ?pq') powr (2 + \<delta>)"
    using pow_le q'real qreal by (simp add: frac_le)
  have err: "\<bar>of_int c * \<alpha> -
      of_int (fst ?pq') / of_int (snd ?pq')\<bar> =
      of_int c * \<bar>\<alpha> - of_int p / of_int q\<bar>"
  proof -
    have "\<bar>of_int c * \<alpha> -
        of_int (fst ?pq') / of_int (snd ?pq')\<bar> =
        \<bar>of_int c * (\<alpha> - of_int p / of_int q)\<bar>"
      by (subst frac) (simp add: algebra_simps)
    then show ?thesis
      using c by (simp add: abs_mult)
  qed
  have "of_int c * \<bar>\<alpha> - of_int p / of_int q\<bar> <
    of_int c * (1 / of_int q powr (2 + \<epsilon>))"
    using near creal by (rule mult_strict_left_mono)
  also have "\<dots> = of_int c / of_int q powr (2 + \<epsilon>)"
    by simp
  also have "\<dots> < 1 / of_int q powr (2 + \<delta>)"
    using bound .
  also have "\<dots> \<le> 1 / of_int (snd ?pq') powr (2 + \<delta>)"
    using inv_le .
  finally have near':
    "\<bar>of_int c * \<alpha> -
      of_int (fst ?pq') / of_int (snd ?pq')\<bar> <
      1 / of_int (snd ?pq') powr (2 + \<delta>)"
    using err by simp
  show ?thesis
    using q'pos cop' near' by (cases ?pq') auto
qed

lemma roth_scaled_pair_inj:
  fixes c p q r s :: int
  assumes c: "c > 0" and q: "q > 0" and s: "s > 0"
    and cop_pq: "coprime p q" and cop_rs: "coprime r s"
    and eq: "roth_scaled_pair c (p,q) = roth_scaled_pair c (r,s)"
  shows "(p,q) = (r,s)"
proof -
  have cross: "(c * p) * s = (c * r) * q"
    using q s eq unfolding roth_scaled_pair_def
    by (intro Rat.normalize_crossproduct) auto
  have cross0: "p * s = r * q"
    using cross c by (simp add: mult_ac)
  have rat_eq: "Fract p q = Fract r s"
    using q s cross0 by (simp add: eq_rat)
  have "(p,q) = quotient_of (Fract p q)"
    using q cop_pq by (simp add: quotient_of_Fract)
  also have "\<dots> = quotient_of (Fract r s)"
    using rat_eq by simp
  also have "\<dots> = (r,s)"
    using s cop_rs by (simp add: quotient_of_Fract)
  finally show ?thesis .
qed

lemma inj_on_roth_scaled_pair:
  fixes c :: int
  assumes "c > 0"
  shows "inj_on (roth_scaled_pair c) (roth_good_pairs \<alpha> \<kappa>)"
proof (rule inj_onI)
  fix x y
  assume x: "x \<in> roth_good_pairs \<alpha> \<kappa>"
    and y: "y \<in> roth_good_pairs \<alpha> \<kappa>"
    and eq: "roth_scaled_pair c x = roth_scaled_pair c y"
  obtain p q where x_def: "x = (p,q)"
    by (cases x) auto
  obtain r s where y_def: "y = (r,s)"
    by (cases y) auto
  show "x = y"
    using roth_scaled_pair_inj[OF assms _ _ _ _ eq[unfolded x_def y_def]]
      x y x_def y_def by auto
qed

theorem finite_roth_good_pairs_of_scaled:
  fixes c :: int and \<alpha> \<epsilon> \<delta> :: real
  assumes c: "c > 0" and eps: "\<epsilon> > \<delta>" and delta: "\<delta> > 0"
    and fin: "finite (roth_good_pairs (of_int c * \<alpha>) (2 + \<delta>))"
  shows "finite (roth_good_pairs \<alpha> (2 + \<epsilon>))"
proof -
  obtain A :: int where A:
    "\<forall>pq\<in>roth_good_pairs (of_int c * \<alpha>) (2 + \<delta>). snd pq \<le> A"
    using fin finite_roth_good_pairs_iff_bounded_denominator by blast
  obtain B :: int where B:
    "\<And>q::int. B \<le> q \<Longrightarrow> of_int c < of_int q powr (\<epsilon> - \<delta>)"
    using roth_powr_threshold[of "of_int c" "\<epsilon> - \<delta>"] c eps
    by auto
  have denom_bound:
    "\<forall>pq\<in>roth_good_pairs \<alpha> (2 + \<epsilon>). snd pq \<le> max B (c * A)"
  proof (intro ballI)
    fix pq
    assume good: "pq \<in> roth_good_pairs \<alpha> (2 + \<epsilon>)"
    obtain p q where pq: "pq = (p,q)"
      by (cases pq) auto
    show "snd pq \<le> max B (c * A)"
    proof (cases "q < B")
      case True
      then show ?thesis
        using pq by simp
    next
      case False
      then have qB: "B \<le> q"
        by simp
      have scaled: "roth_scaled_pair c (p,q) \<in>
          roth_good_pairs (of_int c * \<alpha>) (2 + \<delta>)"
        using roth_scaled_good_pair[OF c eps delta good[unfolded pq] B[OF qB]] .
      have q_le: "q \<le> c * snd (roth_scaled_pair c (p,q))"
        using good c roth_scaled_pair_properties(4)[of c q p]
        by (simp add: pq)
      have scale_le: "snd (roth_scaled_pair c (p,q)) \<le> A"
        using A scaled by blast
      have "c * snd (roth_scaled_pair c (p,q)) \<le> c * A"
        using c scale_le by (intro mult_left_mono) auto
      then show ?thesis
        using pq q_le by simp
    qed
  qed
  show ?thesis
    using denom_bound finite_roth_good_pairs_iff_bounded_denominator by blast
qed

end
