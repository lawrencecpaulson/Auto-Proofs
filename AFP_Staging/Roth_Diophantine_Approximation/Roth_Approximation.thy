theory Roth_Approximation
  imports
    "HOL-Computational_Algebra.Polynomial"
    "HOL-Library.Infinite_Set"
begin

section \<open>Rational approximants to a real number\<close>

definition roth_good_pairs :: "real \<Rightarrow> real \<Rightarrow> (int \<times> int) set" where
  "roth_good_pairs \<alpha> \<kappa> \<equiv>
    {(p,q). q > 0 \<and> coprime p q \<and>
      \<bar>\<alpha> - of_int p / of_int q\<bar> < 1 / of_int q powr \<kappa>}"

lemma roth_good_pairs_iff [simp]:
  "(p,q) \<in> roth_good_pairs \<alpha> \<kappa> \<longleftrightarrow>
    q > 0 \<and> coprime p q \<and>
      \<bar>\<alpha> - of_int p / of_int q\<bar> < 1 / of_int q powr \<kappa>"
  by (simp add: roth_good_pairs_def)

definition roth_good_nat_pairs :: "real \<Rightarrow> real \<Rightarrow> (int \<times> nat) set" where
  "roth_good_nat_pairs \<alpha> \<kappa> \<equiv>
    {(p,q). q > 0 \<and> coprime p (int q) \<and>
      \<bar>\<alpha> - of_int p / of_nat q\<bar> < 1 / of_nat q powr \<kappa>}"

lemma roth_good_pairs_image_nat:
  "roth_good_pairs \<alpha> \<kappa> = (\<lambda>(p,q). (p,int q)) ` roth_good_nat_pairs \<alpha> \<kappa>"
proof
  show "roth_good_pairs \<alpha> \<kappa> \<subseteq> (\<lambda>(p,q). (p,int q)) ` roth_good_nat_pairs \<alpha> \<kappa>"
    using pos_int_cases
    by (fastforce simp: roth_good_nat_pairs_def image_iff)
next
  show "(\<lambda>(p,q). (p,int q)) ` roth_good_nat_pairs \<alpha> \<kappa> \<subseteq> roth_good_pairs \<alpha> \<kappa>"
    by (auto simp: roth_good_nat_pairs_def)
qed

lemma finite_roth_good_nat_pairs_iff:
  "finite (roth_good_nat_pairs \<alpha> \<kappa>) \<longleftrightarrow> finite (roth_good_pairs \<alpha> \<kappa>)"
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
  have pd_lt: "\<bar>of_int p / of_int q\<bar> < \<bar>\<alpha>\<bar> + E"
    using near by linarith
  have "real_of_int \<bar>p\<bar> = of_int q * \<bar>of_int p / of_int q\<bar>"
    using q by (simp add: abs_mult)
  also have "\<dots> < of_int q * (\<bar>\<alpha>\<bar> + E)"
    using pd_lt q by (meson mult_less_cancel_left_disj of_int_pos)
  also have "\<dots> \<le> of_int \<lceil>of_int q * (\<bar>\<alpha>\<bar> + E)\<rceil>"
    by (rule le_of_int_ceiling)
  finally show ?thesis
    by simp
qed

lemma finite_roth_numerators:
  fixes \<alpha> \<kappa> :: real and q :: int
  assumes q: "q > 0"
  shows "finite {p. \<bar>\<alpha> - of_int p / of_int q\<bar> < 1 / of_int q powr \<kappa>}"
proof -
  let ?E = "1 / q powr \<kappa>"
  let ?S = "{p::int. \<bar>\<alpha> - of_int p / of_int q\<bar> < ?E}"
  let ?B = "\<lceil>of_int q * (\<bar>\<alpha>\<bar> + ?E)\<rceil>"
  have "abs ` ?S \<subseteq> {..?B}"
    using rational_approximant_height_bound[OF q] by auto
  then show ?thesis
    by (auto simp: finite_int_iff_bounded_le)
qed

lemma finite_roth_good_pairs_bounded_denominator:
  fixes B :: int
  shows "finite {(p,q) \<in> roth_good_pairs \<alpha> \<kappa>. q \<le> B}"
proof -
  let ?F = "\<lambda>q. {p. (p,q) \<in> roth_good_pairs \<alpha> \<kappa>}"
  have finU: "finite (\<Union>q\<in>{1..B}. (\<lambda>p. (p,q)) ` ?F q)"
    by (simp add: finite_roth_numerators)
  have "{(p,q) \<in> roth_good_pairs \<alpha> \<kappa>. q \<le> B} \<subseteq> (\<Union>q\<in>{1..B}. (\<lambda>p. (p,q)) ` ?F q)"
    by fastforce
  then show ?thesis
    using finU by (rule finite_subset)
qed

lemma finite_roth_good_pairs_iff_bounded_denominator:
  "finite (roth_good_pairs \<alpha> \<kappa>) \<longleftrightarrow> (\<exists>B::int. \<forall>pq\<in>roth_good_pairs \<alpha> \<kappa>. snd pq \<le> B)"
   (is "?L = ?R")
proof
  assume ?L
  then obtain B :: int where B: "abs ` (snd ` roth_good_pairs \<alpha> \<kappa>) \<subseteq> {..B}"
    using finite_int_iff_bounded_le by blast
  show ?R
    using B by fastforce
next
  assume ?R
  then obtain B :: int where  "roth_good_pairs \<alpha> \<kappa> = {(p,q) \<in> roth_good_pairs \<alpha> \<kappa>. q \<le> B}"
    by fastforce
  then show "finite (roth_good_pairs \<alpha> \<kappa>)"
    using finite_roth_good_pairs_bounded_denominator by simp
qed

corollary infinite_roth_good_pairs_iff_unbounded_denominator:
  "infinite (roth_good_pairs \<alpha> \<kappa>) \<longleftrightarrow> (\<forall>B::int. \<exists>pq\<in>roth_good_pairs \<alpha> \<kappa>. B < snd pq)"
  using finite_roth_good_pairs_iff_bounded_denominator
  by (auto simp: not_le)

lemma roth_finite_exponent_iff:
  "(\<forall>\<alpha> \<kappa>. algebraic \<alpha> \<and> \<alpha> \<notin> \<rat> \<and> infinite (roth_good_pairs \<alpha> \<kappa>) \<longrightarrow> \<kappa> \<le> 2) \<longleftrightarrow>
   (\<forall>\<alpha> \<delta>. algebraic \<alpha> \<and> \<alpha> \<notin> \<rat> \<and> \<delta> > 0 \<longrightarrow> finite (roth_good_pairs \<alpha> (2 + \<delta>)))"
   (is "?L = ?R")
proof
  assume h: ?R
  show ?L
    using h by (smt (cvc5, dec_internal_enum_inst_sum))
qed force

section \<open>Scaling reduced approximants\<close>

lemma scaled_gcd:
  fixes c p q :: int
  assumes "coprime p q"
  shows "gcd (c * p) q = gcd c q"
  using assms by (simp add: gcd_mult_left_right_cancel coprime_commute)

lemma roth_scaled_denominator:
  fixes c p q :: int
  assumes c: "c > 0" and q: "q > 0" and cop: "coprime p q"
  defines "g \<equiv> gcd (c * p) q"
  shows "g > 0" "g dvd c" "g dvd q" "q div g > 0" "q \<le> c * (q div g)"
proof -
  have g_eq: "g = gcd c q"
    using cop by (simp add: g_def scaled_gcd)
  have glec: "g \<le> c"
    using c by (simp add: g_eq)
  have "q div g > 0"
    using q by (simp add: g_eq pos_imp_zdiv_pos_iff)
  then show "g > 0" "g dvd c" "g dvd q" "q div g > 0"
    using g_eq by auto
  then show "q \<le> c * (q div g)"
    using glec by fastforce
qed

definition roth_scaled_pair :: "int \<Rightarrow> (int \<times> int) \<Rightarrow> (int \<times> int)" where
  "roth_scaled_pair c pq \<equiv> Rat.normalize (c * fst pq, snd pq)"

lemma roth_scaled_pair_properties:
  fixes c p q :: int
  assumes c: "c > 0" and q: "q > 0" and cop: "coprime p q"
  defines "pq' \<equiv> roth_scaled_pair c (p,q)"
  shows "snd pq' > 0" "coprime (fst pq') (snd pq')"
    "snd pq' \<le> q" "q \<le> c * snd pq'"
    "real_of_int (fst pq') / of_int (snd pq') =
      of_int c * (of_int p / of_int q)"
proof -
  let ?g = "gcd (c * p) q"
  have norm: "pq' = (c * p div ?g, q div ?g)"
    using q by (simp add: pq'_def roth_scaled_pair_def Rat.normalize_def Let_def)
  show "snd pq' > 0"
    by (simp add: c cop norm q roth_scaled_denominator(4))
  show "coprime (fst pq') (snd pq')"
    using norm q by (simp add: div_gcd_coprime)
  show "snd pq' \<le> q" "q \<le> c * snd pq'"
    using roth_scaled_denominator[OF c q cop] norm 
    by (simp_all add: int_div_le_self norm q)
  show "(fst pq') / (snd pq') = c * (p / q)"
    by (simp add: norm of_int_div)
qed

lemma roth_powr_threshold:
  fixes c \<eta> :: real
  assumes c: "c > 0" and \<eta>: "\<eta> > 0"
  obtains B :: int where "B > 0" "\<And>q::int. q \<ge> B \<Longrightarrow> c < of_int q powr \<eta>"
proof -
  obtain B :: int where B: "max 1 (c powr (1 / \<eta>)) < of_int B" and "B > 0"
    by (metis ex_less_of_int max_less_iff_conj of_int_0_less_iff)
  have cpow: "(c powr (1 / \<eta>)) powr \<eta> = c"
    using c \<eta> by (simp add: powr_powr)
  show thesis
  proof (intro that)
    show "c < q powr \<eta>" if "q \<ge> B" for q :: int
    proof -
      have "c powr (1/\<eta>) < q"
        using B that by simp
      then show ?thesis
        using cpow \<eta> by (metis powr_ge_zero powr_less_mono2)
    qed
  qed (use B in auto)
qed

lemma roth_scaled_good_pair:
  fixes c p q :: int and \<alpha> \<epsilon> \<delta> :: real
  assumes c: "c > 0" and \<epsilon>: "\<epsilon> > \<delta>" and \<delta>: "\<delta> > 0"
    and good: "(p,q) \<in> roth_good_pairs \<alpha> (2 + \<epsilon>)"
    and large: "of_int c < of_int q powr (\<epsilon> - \<delta>)"
  shows "roth_scaled_pair c (p,q) \<in> roth_good_pairs (of_int c * \<alpha>) (2 + \<delta>)"
proof -
  let ?pq' = "roth_scaled_pair c (p,q)"
  have q: "q > 0" and cop: "coprime p q"
    and near: "\<bar>\<alpha> - of_int p / of_int q\<bar> < 1 / of_int q powr (2 + \<epsilon>)"
    using good by auto
  obtain q'pos: "snd ?pq' > 0" and cop': "coprime (fst ?pq') (snd ?pq')"
    and q'le: "snd ?pq' \<le> q"
    and frac: "real_of_int (fst ?pq') / of_int (snd ?pq') = of_int c * (of_int p / of_int q)"
    using roth_scaled_pair_properties[OF c q cop] by simp
  have "of_int q powr (2 + \<epsilon>) = of_int q powr (2 + \<delta>) * of_int q powr (\<epsilon> - \<delta>)"
    by (subst powr_add[symmetric]) simp
  then have mult_bound: "of_int c * of_int q powr (2 + \<delta>) < of_int q powr (2 + \<epsilon>)"
    using large q by force
  have pow_le: "of_int (snd ?pq') powr (2 + \<delta>) \<le> of_int q powr (2 + \<delta>)"
    using \<delta> q'pos q'le by (intro powr_mono2) auto
  have err: "\<bar>of_int c * \<alpha> - of_int (fst ?pq') / of_int (snd ?pq')\<bar> =
             of_int c * \<bar>\<alpha> - of_int p / of_int q\<bar>"
    using c by (simp add: frac abs_mult_pos' algebra_simps)
  have "of_int c * \<bar>\<alpha> - of_int p / of_int q\<bar> <
    of_int c * (1 / of_int q powr (2 + \<epsilon>))"
    using near c mult_strict_left_mono by fastforce 
  also have "\<dots> < 1 / of_int q powr (2 + \<delta>)"
    using mult_bound q by (simp add: field_simps)
  also have "\<dots> \<le> 1 / of_int (snd ?pq') powr (2 + \<delta>)"
    using pow_le q'pos q by (simp add: frac_le)
  finally show ?thesis
    using err q'pos cop' by (cases ?pq') auto
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
  then have rat_eq: "Fract p q = Fract r s"
    using c eq_rat q s by force
  have "(p,q) = quotient_of (Fract p q)"
    using q cop_pq by (simp add: quotient_of_Fract)
  then show ?thesis
    by (simp add: cop_rs quotient_of_Fract rat_eq s)
qed

theorem finite_roth_good_pairs_of_scaled:
  fixes c :: int and \<alpha> \<epsilon> \<delta> :: real
  assumes c: "c > 0" and \<epsilon>: "\<epsilon> > \<delta>" and \<delta>: "\<delta> > 0"
    and fin: "finite (roth_good_pairs (of_int c * \<alpha>) (2 + \<delta>))"
  shows "finite (roth_good_pairs \<alpha> (2 + \<epsilon>))"
proof -
  obtain A :: int where A:
    "\<forall>pq\<in>roth_good_pairs (of_int c * \<alpha>) (2 + \<delta>). snd pq \<le> A"
    using fin finite_roth_good_pairs_iff_bounded_denominator by blast
  obtain B :: int where B: "\<And>q::int. B \<le> q \<Longrightarrow> of_int c < of_int q powr (\<epsilon> - \<delta>)"
    using roth_powr_threshold[of "of_int c" "\<epsilon> - \<delta>"] c \<epsilon>
    by auto
  have "snd pq \<le> max B (c * A)" if good: "pq \<in> roth_good_pairs \<alpha> (2 + \<epsilon>)" for pq
  proof -
    obtain p q where pq: "pq = (p,q)"
      by (cases pq) auto
    show ?thesis
    proof (cases "q < B")
      case True
      then show ?thesis
        using pq by simp
    next
      case False
      then have scale_le: "snd (roth_scaled_pair c (p,q)) \<le> A"
        using roth_scaled_good_pair[OF c \<epsilon> \<delta> good[unfolded pq] B]
        using A by auto
      have q_le: "q \<le> c * snd (roth_scaled_pair c (p,q))"
        using good c roth_scaled_pair_properties(4)[of c q p]
        by (simp add: pq)
      then show ?thesis
        using c pq scale_le by (smt (verit, best) mult_le_cancel_left sndI)
    qed
  qed
  then show ?thesis
    using finite_roth_good_pairs_iff_bounded_denominator by blast
qed

end
