theory Roth_Approximation_Height
  imports Roth_Approximant_Selection
begin

lemma roth_good_pair_height_le:
  fixes alpha kappa :: real and p q :: int
  assumes good: "(p,q) \<in> roth_good_pairs alpha kappa"
    and kap: "0 \<le> kappa"
  shows "real (roth_rat_height (Rat.Fract p q)) \<le>
    (abs alpha + 1) * real_of_int q"
proof -
  have q: "0 < q" and cop: "coprime p q"
    and near: "abs (alpha - real_of_int p / real_of_int q) <
      1 / real_of_int q powr kappa"
    using good by auto
  have qr: "1 \<le> (real_of_int q :: real)" using q by simp
  have "1 powr kappa \<le> real_of_int q powr kappa"
    by (intro powr_mono2) (use qr kap in auto)
  then have qpow: "1 \<le> real_of_int q powr kappa" by simp
  have inv: "1 / real_of_int q powr kappa \<le> 1"
    using qpow by (simp add: divide_le_eq)
  have near1: "abs (alpha - real_of_int p / real_of_int q) < 1"
    using near inv by linarith
  have ratbound: "abs (real_of_int p / real_of_int q) < abs alpha + 1"
    using near1 by linarith
  have abs_p: "abs (real_of_int p) < (abs alpha + 1) * real_of_int q"
  proof -
    have "abs (real_of_int p) = real_of_int q *
        abs (real_of_int p / real_of_int q)"
      using q by (simp add: abs_divide)
    also have "... < real_of_int q * (abs alpha + 1)"
      using q ratbound by (intro mult_strict_left_mono) auto
    finally show ?thesis by (simp add: mult.commute)
  qed
  have h: "roth_rat_height (Rat.Fract p q) = nat (max (abs p) q)"
    using q cop by (simp add: roth_rat_height_Fract)
  have hreal: "real (roth_rat_height (Rat.Fract p q)) =
      max (abs (real_of_int p)) (real_of_int q)"
    using q by (simp add: h)
  have qbound: "real_of_int q \<le> (abs alpha + 1) * real_of_int q"
    using qr by (simp add: distrib_right)
  show ?thesis using abs_p qbound hreal by simp
qed

lemma roth_good_pair_near_height_abstract:
  fixes alpha kappa kappa' :: real and p q :: int
  assumes good: "(p,q) \<in> roth_good_pairs alpha kappa"
    and power: "real (roth_rat_height (Rat.Fract p q)) powr kappa' <
      real_of_int q powr kappa"
  shows "abs (of_rat (Rat.Fract p q) - alpha) \<le>
    exp (-kappa' * roth_rat_log_height (Rat.Fract p q))"
proof -
  let ?H = "real (roth_rat_height (Rat.Fract p q))"
  have q: "0 < q" using good by simp
  have Hpos: "0 < ?H" by simp
  have qpow: "0 < real_of_int q powr kappa" using q by simp
  have Hpow: "0 < ?H powr kappa'" using Hpos by simp
  have frac: "of_rat (Rat.Fract p q) = (real_of_int p / real_of_int q :: real)"
    using q by (simp add: of_rat_rat)
  have near: "abs (of_rat (Rat.Fract p q) - alpha) <
      1 / real_of_int q powr kappa"
    using good frac by (simp add: abs_minus_commute)
  have inv: "1 / real_of_int q powr kappa < 1 / ?H powr kappa'"
    using power Hpow qpow by (simp add: divide_strict_left_mono)
  have form: "1 / ?H powr kappa' =
      exp (-kappa' * roth_rat_log_height (Rat.Fract p q))"
    using Hpos by (simp add: roth_rat_log_height_def powr_def exp_minus inverse_eq_divide)
  show ?thesis using near inv form by linarith
qed


lemma roth_good_pair_near_height_threshold:
  fixes alpha kappa kappa' :: real and p q :: int
  assumes good: "(p,q) \<in> roth_good_pairs alpha kappa"
    and kap: "0 < kappa'" "kappa' < kappa"
    and threshold: "(abs alpha + 1) powr kappa' <
      real_of_int q powr (kappa - kappa')"
  shows "abs (of_rat (Rat.Fract p q) - alpha) \<le>
    exp (-kappa' * roth_rat_log_height (Rat.Fract p q))"
proof -
  let ?H = "real (roth_rat_height (Rat.Fract p q))"
  let ?C = "abs alpha + 1"
  have q: "0 < q" using good by simp
  have qr: "0 < (real_of_int q :: real)" using q by simp
  have Cpos: "0 < ?C" by simp
  have Hpos: "0 < ?H" by simp
  have Hle: "?H \<le> ?C * real_of_int q"
    using roth_good_pair_height_le[OF good] kap by auto
  have Hpow: "?H powr kappa' \<le> (?C * real_of_int q) powr kappa'"
    by (rule powr_mono2) (use Hle kap Hpos in auto)
  have Ceq: "(?C * real_of_int q) powr kappa' =
      ?C powr kappa' * real_of_int q powr kappa'"
    using Cpos qr by (simp add: powr_mult)
  have strict: "?C powr kappa' * real_of_int q powr kappa' <
      real_of_int q powr (kappa - kappa') * real_of_int q powr kappa'"
    using threshold qr by (intro mult_strict_right_mono) auto
  have qeq: "real_of_int q powr (kappa - kappa') * real_of_int q powr kappa' =
      real_of_int q powr kappa"
    using qr by (simp add: powr_add [symmetric])
  have power: "?H powr kappa' < real_of_int q powr kappa"
    using Hpow strict Ceq qeq by linarith
  show ?thesis
    by (rule roth_good_pair_near_height_abstract[OF good power])
qed

theorem roth_good_pair_near_height_eventual:
  fixes alpha kappa kappa' :: real
  assumes kap: "0 < kappa'" "kappa' < kappa"
  obtains B :: int where "0 < B" and
    "\<And>p q. (p,q) \<in> roth_good_pairs alpha kappa \<Longrightarrow> B \<le> q \<Longrightarrow>
      abs (of_rat (Rat.Fract p q) - alpha) \<le>
        exp (-kappa' * roth_rat_log_height (Rat.Fract p q))"
proof -
  let ?C = "(abs alpha + 1) powr kappa'"
  have Cpos: "0 < ?C" by simp
  have eta: "0 < kappa - kappa'" using kap by simp
  obtain B :: int where Bpos: "0 < B" and threshold:
      "\<And>q::int. B \<le> q \<Longrightarrow> ?C < real_of_int q powr (kappa-kappa')"
    using roth_powr_threshold[of ?C "kappa-kappa'"] Cpos eta by blast
  have near: "abs (of_rat (Rat.Fract p q) - alpha) \<le>
      exp (-kappa' * roth_rat_log_height (Rat.Fract p q))"
    if good: "(p,q) \<in> roth_good_pairs alpha kappa" and large: "B \<le> q"
    for p q
    by (rule roth_good_pair_near_height_threshold[OF good kap
      threshold[OF large]])
  show thesis by (rule that[OF Bpos near])
qed


lemma roth_good_pairs_unbounded_log_height_with_q:
  fixes Q :: int
  assumes inf: "infinite (roth_good_pairs alpha kappa)"
  shows "\<forall>B::real. \<exists>p q. (p,q) \<in> roth_good_pairs alpha kappa \<and>
    Q \<le> q \<and> B < roth_rat_log_height (Rat.Fract p q)"
proof
  fix B :: real
  obtain N :: int where N: "max (real_of_int Q) (exp B) < real_of_int N"
    using ex_less_of_int by blast
  obtain pq where good: "pq \<in> roth_good_pairs alpha kappa"
    and large: "N < snd pq"
    using infinite_roth_good_pairs_iff_unbounded_denominator[of alpha kappa]
      inf by blast
  obtain p q where pq: "pq = (p,q)" by (cases pq) auto
  have good': "(p,q) \<in> roth_good_pairs alpha kappa"
    using good pq by simp
  have q: "0 < q" and cop: "coprime p q" using good' by auto
  have qQ: "Q \<le> q" and qB: "exp B < real_of_int q"
    using large pq N by auto
  have h: "roth_rat_height (Rat.Fract p q) = nat (max (abs p) q)"
    using q cop by (simp add: roth_rat_height_Fract)
  have qle: "real_of_int q \<le> real (roth_rat_height (Rat.Fract p q))"
    using q by (simp add: h)
  have "exp B < real (roth_rat_height (Rat.Fract p q))"
    using qB qle by linarith
  then have "ln (exp B) < ln (real (roth_rat_height (Rat.Fract p q)))"
    by (intro ln_strict_mono) simp_all
  then show "\<exists>p q. (p,q) \<in> roth_good_pairs alpha kappa \<and>
    Q \<le> q \<and> B < roth_rat_log_height (Rat.Fract p q)"
    using good' qQ by (metis ln_exp roth_rat_log_height_def)
qed

theorem roth_select_near_rationals:
  assumes inf: "infinite (roth_good_pairs alpha kappa)"
    and kap: "0 < kappa'" "kappa' < kappa"
  shows "\<exists>beta :: nat \<Rightarrow> rat.
    (\<forall>v<m. B < roth_rat_log_height (beta v) \<and>
      abs (of_rat (beta v) - alpha) \<le>
        exp (-kappa' * roth_rat_log_height (beta v))) \<and>
    (\<forall>v. Suc v < m \<longrightarrow>
      K * roth_rat_log_height (beta v) <
        roth_rat_log_height (beta (Suc v)))"
proof -
  let ?C = "(abs alpha + 1) powr kappa'"
  have Cpos: "0 < ?C" by simp
  have eta: "0 < kappa - kappa'" using kap by simp
  obtain Q :: int where Qpos: "0 < Q" and threshold:
      "\<And>q::int. Q \<le> q \<Longrightarrow> ?C < real_of_int q powr (kappa-kappa')"
    using roth_powr_threshold[of ?C "kappa-kappa'"] Cpos eta by blast
  have near: "abs (of_rat (Rat.Fract p q) - alpha) \<le>
      exp (-kappa' * roth_rat_log_height (Rat.Fract p q))"
    if good: "(p,q) \<in> roth_good_pairs alpha kappa" and large: "Q \<le> q"
    for p q
    by (rule roth_good_pair_near_height_threshold[OF good kap
      threshold[OF large]])
  let ?S = "{pq \<in> roth_good_pairs alpha kappa. Q \<le> snd pq}"
  let ?h = "\<lambda>pq. roth_rat_log_height (Rat.Fract (fst pq) (snd pq))"
  have unb: "\<And>C::real. \<exists>pq\<in>?S. C < ?h pq"
  proof -
    fix C :: real
    obtain p q where good: "(p,q) \<in> roth_good_pairs alpha kappa"
      and qlarge: "Q \<le> q" and hlarge:
      "C < roth_rat_log_height (Rat.Fract p q)"
      using roth_good_pairs_unbounded_log_height_with_q[OF inf,
        rule_format, of Q C] by blast
    show "\<exists>pq\<in>?S. C < ?h pq"
      by (rule bexI[where x="(p,q)"]) (use good qlarge hlarge in simp_all)
  qed
  obtain pq :: "nat \<Rightarrow> int \<times> int" where members:
      "\<forall>v<m. pq v \<in> ?S \<and> B < ?h (pq v)" and growth:
      "\<forall>v. Suc v < m \<longrightarrow> K * ?h (pq v) < ?h (pq (Suc v))"
    using roth_unbounded_sequence[OF unb, of m B K] by blast
  let ?beta = "\<lambda>v. Rat.Fract (fst (pq v)) (snd (pq v))"
  have betamember: "\<forall>v<m. B < roth_rat_log_height (?beta v) \<and>
      abs (of_rat (?beta v) - alpha) \<le>
        exp (-kappa' * roth_rat_log_height (?beta v))"
  proof (intro allI impI conjI)
    fix v
    assume vm: "v < m"
    have mem: "pq v \<in> ?S" and large: "B < ?h (pq v)"
      using members vm by auto
    have good: "(fst (pq v), snd (pq v)) \<in> roth_good_pairs alpha kappa"
      using mem by (cases "pq v") simp
    have qlarge: "Q \<le> snd (pq v)" using mem by simp
    show "B < roth_rat_log_height (?beta v)" using large by simp
    show "abs (of_rat (?beta v) - alpha) \<le>
        exp (-kappa' * roth_rat_log_height (?beta v))"
      by (rule near[OF good qlarge])
  qed
  show ?thesis
    by (rule exI[of _ ?beta]) (use betamember growth in simp)
qed

end
