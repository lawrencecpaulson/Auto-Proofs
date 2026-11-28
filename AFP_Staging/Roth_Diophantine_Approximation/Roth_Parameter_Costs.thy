theory Roth_Parameter_Costs
  imports
    Auxiliary_Index_Transfer
begin

lemma roth_unbounded_sequence:
  fixes S :: "'a set" and h :: "'a \<Rightarrow> real"
  assumes unbounded: "\<And>B. \<exists>x\<in>S. B < h x"
  shows "\<exists>xs :: nat \<Rightarrow> 'a. (\<forall>v<m. xs v \<in> S \<and> B < h (xs v)) \<and>
    (\<forall>v. Suc v < m \<longrightarrow> K * h (xs v) < h (xs (Suc v)))"
proof (induct m)
  case 0
  obtain x where xS: "x \<in> S" using unbounded[of B] by blast
  show ?case by (intro exI[of _ "\<lambda>_. x"]) simp
next
  case (Suc m)
  obtain xs :: "nat \<Rightarrow> 'a" where old: "\<forall>v<m. xs v \<in> S \<and> B < h (xs v)" 
    and growth: "\<forall>v. Suc v < m \<longrightarrow> K * h (xs v) < h (xs (Suc v))"
    using Suc.hyps by blast
  obtain x where xS: "x \<in> S" and xbig:
      "max B (K * h (xs (m-1))) < h x"
    using unbounded[of "max B (K * h (xs (m-1)))"] by blast
  let ?ys = "xs(m := x)"
  have members: "\<forall>v<Suc m. ?ys v \<in> S \<and> B < h (?ys v)"
    using old xS xbig by (auto simp: less_Suc_eq)
  have grows: "\<forall>v. Suc v < Suc m \<longrightarrow>
      K * h (?ys v) < h (?ys (Suc v))"
  proof (intro allI impI)
    fix v
    assume vm: "Suc v < Suc m"
    then have vlt: "v < m" by simp
    show "K * h (?ys v) < h (?ys (Suc v))"
    proof (cases "Suc v < m")
      case True
      then show ?thesis using growth vlt by simp
    next
      case False
      with vm have eq: "Suc v = m" by simp
      then have "v = m-1" by simp
      with xbig vlt eq show ?thesis by simp
    qed
  qed
  show ?case using members grows by blast
qed

definition roth_rounded_degrees :: "real \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat" where
  "roth_rounded_degrees T h v = nat (ceiling (T / h v))"

lemma roth_rounded_degrees_bounds:
  assumes Tpos: "0 < T" and hpos: "0 < h v"
  shows "0 < roth_rounded_degrees T h v"
    "T \<le> real (roth_rounded_degrees T h v) * h v"
    "real (roth_rounded_degrees T h v) * h v \<le> T + h v"
proof -
  let ?z = "T / h v"
  have zpos: "0 < ?z" using Tpos hpos by simp
  have cpos: "0 < ceiling ?z" using zpos by simp
  have real_eq: "real (roth_rounded_degrees T h v) = real_of_int (ceiling ?z)"
    using cpos by (simp add: roth_rounded_degrees_def)
  show "0 < roth_rounded_degrees T h v" using cpos
    by (simp add: roth_rounded_degrees_def)
  show "T \<le> real (roth_rounded_degrees T h v) * h v"
    using real_eq hpos by (metis ceiling_divide_upper) 
  have "real (roth_rounded_degrees T h v) * h v \<le> (?z + 1) * h v"
    using real_eq hpos by (intro mult_right_mono) auto
  also have "... = T + h v" using hpos by (simp add: distrib_right)
  finally show "real (roth_rounded_degrees T h v) * h v \<le> T + h v" .
qed

lemma roth_rounded_degrees_ratio:
  fixes h :: "nat \<Rightarrow> real"
  assumes Tpos: "0 < T" and hpos: "0 < h v" "0 < h (Suc v)"
    and sig: "0 \<le> sigma"
    and gap: "T / h (Suc v) + 1 \<le> sigma * (T / h v)"
  shows "real (roth_rounded_degrees T h (Suc v)) \<le>
    sigma * real (roth_rounded_degrees T h v)"
proof -
  have upper: "real (roth_rounded_degrees T h (Suc v)) \<le> T / h (Suc v) + 1"
    using Tpos hpos(2) by (simp add: roth_rounded_degrees_def)
  have lower: "T / h v \<le> real (roth_rounded_degrees T h v)"
    using roth_rounded_degrees_bounds(2)[of T h v] Tpos hpos(1)
    by (simp add: divide_le_eq)
  have "sigma * (T / h v) \<le> sigma * real (roth_rounded_degrees T h v)"
    by (rule mult_left_mono[OF lower sig])
  then show ?thesis using upper gap by linarith
qed

lemma roth_good_pair_height_le:
  fixes \<alpha> kappa :: real and p q :: int
  assumes good: "(p,q) \<in> roth_good_pairs \<alpha> kappa"
    and kap: "0 \<le> kappa"
  shows "real (pheight_rat_height (Rat.Fract p q)) \<le> (abs \<alpha> + 1) * real_of_int q"
proof -
  have q: "0 < q" and cop: "coprime p q"
    and near: "abs (\<alpha> - p / q) < 1 / q powr kappa"
    using good by auto
  have qr: "1 \<le> real_of_int q" using q by simp
  have "1 powr kappa \<le> real_of_int q powr kappa"
    by (intro powr_mono2) (use qr kap in auto)
  then have qpow: "1 \<le> real_of_int q powr kappa" by simp
  have inv: "1 / real_of_int q powr kappa \<le> 1"
    using qpow by (simp add: divide_le_eq)
  have ratbound: "abs (real_of_int p / real_of_int q) < abs \<alpha> + 1"
    using near inv by linarith
  have abs_p: "abs (real_of_int p) < (abs \<alpha> + 1) * real_of_int q"
    using q ratbound by (metis abs_div_pos of_int_0_less_iff pos_divide_less_eq)
  have hreal: "real (pheight_rat_height (Rat.Fract p q)) = max (abs (real_of_int p)) (real_of_int q)"
    using q cop by (simp add: pheight_rat_height_Fract)
  have qbound: "real_of_int q \<le> (abs \<alpha> + 1) * real_of_int q"
    using qr by (simp add: distrib_right)
  show ?thesis using abs_p qbound hreal by simp
qed

lemma roth_good_pair_near_height_abstract:
  fixes \<alpha> kappa kappa' :: real and p q :: int
  assumes good: "(p,q) \<in> roth_good_pairs \<alpha> kappa"
    and power: "real (pheight_rat_height (Rat.Fract p q)) powr kappa' < q powr kappa"
  shows "abs (of_rat (Rat.Fract p q) - \<alpha>) \<le> exp (-kappa' * pheight_rat_log_height (Rat.Fract p q))"
proof -
  let ?H = "real (pheight_rat_height (Rat.Fract p q))"
  have q: "0 < q" using good by simp
  have Hpos: "0 < ?H" by simp
  have qpow: "0 < real_of_int q powr kappa" using q by simp
  have Hpow: "0 < ?H powr kappa'" using Hpos by simp
  have frac: "of_rat (Rat.Fract p q) = (real_of_int p / real_of_int q :: real)"
    using q by (simp add: of_rat_rat)
  have near: "abs (of_rat (Rat.Fract p q) - \<alpha>) < 1 / q powr kappa"
    using good frac by (simp add: abs_minus_commute)
  have inv: "1 / real_of_int q powr kappa < 1 / ?H powr kappa'"
    using power Hpow qpow by (simp add: divide_strict_left_mono)
  have form: "1 / ?H powr kappa' =
      exp (-kappa' * pheight_rat_log_height (Rat.Fract p q))"
    using Hpos by (simp add: pheight_rat_log_height_def powr_def exp_minus inverse_eq_divide)
  show ?thesis using near inv form by linarith
qed


lemma roth_good_pair_near_height_threshold:
  fixes \<alpha> kappa kappa' :: real and p q :: int
  assumes good: "(p,q) \<in> roth_good_pairs \<alpha> kappa"
    and kap: "0 < kappa'" "kappa' < kappa"
    and threshold: "(abs \<alpha> + 1) powr kappa' <
      real_of_int q powr (kappa - kappa')"
  shows "abs (of_rat (Rat.Fract p q) - \<alpha>) \<le> exp (-kappa' * pheight_rat_log_height (Rat.Fract p q))"
proof -
  let ?H = "real (pheight_rat_height (Rat.Fract p q))"
  let ?C = "abs \<alpha> + 1"
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

lemma roth_good_pairs_unbounded_log_height_with_q:
  fixes Q :: int
  assumes inf: "infinite (roth_good_pairs \<alpha> kappa)"
  shows "\<exists>p q. (p,q) \<in> roth_good_pairs \<alpha> kappa \<and> Q \<le> q \<and> B < pheight_rat_log_height (Rat.Fract p q)"
proof -
  obtain N :: int where N: "max Q (exp B) < real_of_int N"
    using ex_less_of_int by blast
  obtain pq where good: "pq \<in> roth_good_pairs \<alpha> kappa"
    and large: "N < snd pq"
    using infinite_roth_good_pairs_iff_unbounded_denominator[of \<alpha> kappa]
      inf by blast
  obtain p q where pq: "pq = (p,q)" and q: "0 < q" and cop: "coprime p q"  
    using good by (cases pq) auto
  have qQ: "Q \<le> q" and qB: "exp B < real_of_int q"
    using large pq N by auto
  have h: "pheight_rat_height (Rat.Fract p q) = nat (max (abs p) q)"
    using q cop by (simp add: pheight_rat_height_Fract)
  have qle: "real_of_int q \<le> real (pheight_rat_height (Rat.Fract p q))"
    using q by (simp add: h)
  have "exp B < real (pheight_rat_height (Rat.Fract p q))"
    using qB qle by linarith
  then have "ln (exp B) < ln (real (pheight_rat_height (Rat.Fract p q)))"
    by (intro ln_strict_mono) simp_all
  then show ?thesis
    by (metis good pq qQ ln_unique pheight_rat_log_height_def)
qed

theorem roth_select_near_rationals:
  assumes inf: "infinite (roth_good_pairs \<alpha> kappa)"
    and kap: "0 < kappa'" "kappa' < kappa"
  shows "\<exists>\<beta> :: nat \<Rightarrow> rat.
    (\<forall>v<m. B < pheight_rat_log_height (\<beta> v) \<and>
      abs (of_rat (\<beta> v) - \<alpha>) \<le> exp (-kappa' * pheight_rat_log_height (\<beta> v))) \<and>
    (\<forall>v. Suc v < m \<longrightarrow>
      K * pheight_rat_log_height (\<beta> v) < pheight_rat_log_height (\<beta> (Suc v)))"
proof -
  let ?C = "(abs \<alpha> + 1) powr kappa'"
  have Cpos: "0 < ?C" by simp
  have eta: "0 < kappa - kappa'" using kap by simp
  obtain Q :: int where Qpos: "0 < Q" and threshold:
      "\<And>q::int. Q \<le> q \<Longrightarrow> ?C < q powr (kappa-kappa')"
    using roth_powr_threshold[of ?C "kappa-kappa'"] Cpos eta by blast
  have near: "abs (of_rat (Rat.Fract p q) - \<alpha>) \<le>
      exp (-kappa' * pheight_rat_log_height (Rat.Fract p q))"
    if good: "(p,q) \<in> roth_good_pairs \<alpha> kappa" and large: "Q \<le> q"
    for p q
    by (rule roth_good_pair_near_height_threshold[OF good kap
      threshold[OF large]])
  let ?S = "{pq \<in> roth_good_pairs \<alpha> kappa. Q \<le> snd pq}"
  let ?h = "\<lambda>pq. pheight_rat_log_height (Rat.Fract (fst pq) (snd pq))"
  have unb: "\<exists>pq\<in>?S. C < ?h pq" for C
    using roth_good_pairs_unbounded_log_height_with_q[OF inf, of Q C] 
    by force
  obtain pq :: "nat \<Rightarrow> int \<times> int" where members:
      "\<forall>v<m. pq v \<in> ?S \<and> B < ?h (pq v)" and growth:
      "\<forall>v. Suc v < m \<longrightarrow> K * ?h (pq v) < ?h (pq (Suc v))"
    using roth_unbounded_sequence[OF unb, of m B K] by blast
  let ?beta = "\<lambda>v. Rat.Fract (fst (pq v)) (snd (pq v))"
  have betamember: "B < pheight_rat_log_height (?beta v) \<and>
      abs (of_rat (?beta v) - \<alpha>) \<le> exp (-kappa' * pheight_rat_log_height (?beta v))"
    if "v<m" for v
    using members near that by (cases "pq v") auto
  with growth show ?thesis
    by (intro exI[of _ ?beta]) auto
qed

lemma roth_ratio_gap_from_growth:
  fixes h :: "nat \<Rightarrow> real"
  assumes Tpos: "0 < T" and hpos: "0 < h v" "0 < h (Suc v)"
    and sig: "0 < sigma"
    and growth: "2 * h v \<le> sigma * h (Suc v)"
    and large: "2 * h v \<le> sigma * T"
  shows "T / h (Suc v) + 1 \<le> sigma * (T / h v)"
proof -
  have first: "T / h (Suc v) \<le> (sigma / 2) * (T / h v)"
    using Tpos hpos sig growth by (simp add: field_simps)
  have second: "1 \<le> (sigma / 2) * (T / h v)"
    using hpos sig large by (simp add: field_simps)
  have "T / h (Suc v) + 1 \<le> (sigma / 2) * (T / h v) + (sigma / 2) * (T / h v)"
    using first second by linarith
  also have "... = sigma * (T / h v)" by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma roth_rounded_degrees_ratios:
  fixes h :: "nat \<Rightarrow> real"
  assumes Tpos: "0 < T" and sig: "0 < sigma"
    and hpos: "\<And>v. v < m \<Longrightarrow> 0 < h v"
    and growth: "\<And>v. Suc v < m \<Longrightarrow> 2 * h v \<le> sigma * h (Suc v)"
    and large: "\<And>v. v < m \<Longrightarrow> 2 * h v \<le> sigma * T"
    and vm: "Suc v < m"
  shows "real (roth_rounded_degrees T h (Suc v)) \<le>
      sigma * real (roth_rounded_degrees T h v)"
proof -
  have hv: "0 < h v" using hpos vm by simp
  have hn: "0 < h (Suc v)" by (rule hpos[OF vm])
  have gap: "T / h (Suc v) + 1 \<le> sigma * (T / h v)"
    by (rule roth_ratio_gap_from_growth[OF Tpos hv hn sig
      growth[OF vm] large[of v]]) (use vm in simp)
  show "real (roth_rounded_degrees T h (Suc v)) \<le> sigma * real (roth_rounded_degrees T h v)"
    using sig by (intro roth_rounded_degrees_ratio[OF Tpos hv hn _ gap]) auto
qed


lemma roth_choose_large_T:
  fixes h :: "nat \<Rightarrow> real"
  assumes sig: "0 < sigma"
  shows "\<exists>T::real. 0 < T \<and> (\<forall>v<m. 2 * h v \<le> sigma * T)"
proof -
  let ?M = "Max (insert 0 (h ` {..<m}))"
  have Mnonneg: "0 \<le> ?M" by (rule Max_ge) simp_all
  have hle: "h v \<le> ?M" if vm: "v < m" for v
    by (rule Max_ge) (use vm in auto)
  let ?T = "2 * ?M / sigma + 1"
  have Tpos: "0 < ?T" using Mnonneg sig
    by (smt (verit, del_insts) divide_nonneg_nonneg) 
  have bound: "2 * h v \<le> sigma * ?T" if vm: "v < m" for v
    using hle[OF vm] sig by (simp add: distrib_left)
  show ?thesis using Tpos bound by blast
qed

lemma roth_choose_large_T_above:
  fixes h :: "nat \<Rightarrow> real"
  assumes sig: "0 < sigma"
  shows "\<exists>T::real. A < T \<and> 0 < T \<and> (\<forall>v<m. 2 * h v \<le> sigma * T)"
proof -
  obtain T0 :: real where T0pos: "0 < T0" and bound0:
      "\<forall>v<m. 2 * h v \<le> sigma * T0"
    using roth_choose_large_T[where h=h and m=m, OF sig] by blast
  let ?T = "T0 + max A 0 + 1"
  have Tpos: "0 < ?T" and TA: "A < ?T"
    using T0pos by auto
  have b: "2 * h v \<le> sigma * ?T" if vm: "v < m" for v
    using assms bound0 vm by (smt (verit) mult_left_mono)
  show ?thesis using Tpos TA b by blast
qed

lemma roth_degree_uniform:
  fixes h :: "nat \<Rightarrow> real"
  assumes Tpos: "0 < T" and Bpos: "0 < B" and xipos: "0 \<le> xi"
    and hbound: "B \<le> h v" "h v \<le> xi * T"
  shows "T \<le> real (roth_rounded_degrees T h v) * h v"
    "real (roth_rounded_degrees T h v) * h v \<le> (1+xi)*T"
    "real (roth_rounded_degrees T h v) \<le> (1+xi)*T/B"
proof -
  have hpos: "0 < h v" using hbound Bpos by linarith
  show "T \<le> real (roth_rounded_degrees T h v) * h v" 
    using roth_rounded_degrees_bounds(2)[of T h v] Tpos hpos by simp
  have hi: "real (roth_rounded_degrees T h v) * h v \<le> T + h v"
    using roth_rounded_degrees_bounds(3)[of T h v] Tpos hpos by simp
  show w: "real (roth_rounded_degrees T h v) * h v \<le> (1+xi)*T" 
    using hi hbound by (simp add: algebra_simps)
  have B_le: "real (roth_rounded_degrees T h v) * B \<le>
      real (roth_rounded_degrees T h v) * h v"
    using hbound by (intro mult_left_mono) auto
  show "real (roth_rounded_degrees T h v) \<le> (1+xi)*T/B"
    using B_le w Bpos by (simp add: le_divide_eq)
qed

lemma roth_degree_sum:
  fixes h :: "nat \<Rightarrow> real"
  assumes Tpos: "0 < T" and Bpos: "0 < B" and xipos: "0 \<le> xi"
    and hbound: "\<And>v. v < m \<Longrightarrow> B \<le> h v \<and> h v \<le> xi * T"
  shows "real (\<Sum>v<m. roth_rounded_degrees T h v) \<le> m * ((1+xi)*T/B)"
proof -
  have each: "real (roth_rounded_degrees T h v) \<le> (1+xi)*T/B"
    if vm: "v < m" for v
    using roth_degree_uniform(3)[of T B xi h v] Tpos Bpos xipos
      hbound[OF vm] by auto
  have "(\<Sum>v<m. real (roth_rounded_degrees T h v)) \<le> (\<Sum>v<m. (1+xi)*T/B)"
    by (intro sum_mono) (use each in auto)
  then show ?thesis by simp
qed


theorem roth_choose_degrees_above:
  fixes h :: "nat \<Rightarrow> real"
  assumes sig: "0 < sigma" and xi: "0 < xi" and Bpos: "0 < B"
    and hlow: "\<And>v. v < m \<Longrightarrow> B \<le> h v"
    and growth: "\<And>v. Suc v < m \<Longrightarrow>
      2 * h v \<le> sigma * h (Suc v)"
  shows "\<exists>T r. A < (T::real) \<and> 0 < T \<and>
    (\<forall>v<m. 0 < r v \<and> B \<le> h v \<and> h v \<le> xi * T \<and>
      T \<le> real (r v) * h v \<and>
      real (r v) * h v \<le> (1+xi)*T) \<and>
    (\<forall>v. Suc v < m \<longrightarrow> real (r (Suc v)) \<le> sigma * real (r v)) \<and>
    real (\<Sum>v<m. r v) \<le> real m * ((1+xi)*T/B)"
proof -
  let ?M = "Max (insert 0 (h ` {..<m}))"
  have hle: "h v \<le> ?M" if vm: "v < m" for v
    by (rule Max_ge) (use vm in auto)
  obtain T :: real where TA: "A < T" and div: "?M / xi < T" and Tpos: "0 < T"
    and large: "\<And>v. v < m \<Longrightarrow> 2 * h v \<le> sigma * T"
    using roth_choose_large_T_above[where h=h and m=m and A="max A (?M/xi)", OF sig]
    by auto
  have MT: "?M < xi * T"
    using xi div by (metis mult.commute pos_divide_less_eq)
  have hsmall: "h v \<le> xi * T" if vm: "v < m" for v
    using hle[OF vm] MT by linarith
  let ?r = "roth_rounded_degrees T h"
  have hpos: "0 < h v" if vm: "v < m" for v
    using hlow[OF vm] Bpos by linarith
  have bounds: "\<forall>v<m. 0 < ?r v \<and> B \<le> h v \<and> h v \<le> xi * T \<and>
      T \<le> ?r v * h v \<and> ?r v * h v \<le> (1+xi)*T"
  proof (intro allI impI conjI)
    fix v
    assume vm: "v < m"
    show "0 < ?r v" using roth_rounded_degrees_bounds(1)[of T h v] Tpos hpos vm by metis
    show "T \<le> ?r v * h v"
      using roth_rounded_degrees_bounds(2)[of T h v] Tpos hpos vm by metis 
    show "?r v * h v \<le> (1+xi)*T"
      using roth_degree_uniform(2)[of T B xi h v] Tpos Bpos xi hlow[OF vm]
        hsmall[OF vm] by simp
  qed (use hlow hsmall in auto)
  have ratios: "\<forall>v. Suc v < m \<longrightarrow> ?r (Suc v) \<le> sigma * ?r v"
    using roth_rounded_degrees_ratios[where T=T and sigma=sigma and h=h and m=m]
      Tpos sig hpos growth large by blast
  have sumb: "real (\<Sum>v<m. ?r v) \<le> real m * ((1+xi)*T/B)"
    using hlow hsmall xi
    by (intro roth_degree_sum[OF Tpos Bpos _]) auto
  show ?thesis using TA Tpos bounds ratios sumb by blast
qed


text \<open>A selected parameter family combines approximation quality,
balanced degrees, separation of successive degrees, and a total degree
budget.\<close>

definition roth_selected_parameters ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
    real \<Rightarrow> (nat \<Rightarrow> rat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  where
  "roth_selected_parameters \<alpha> kappa' m B xi sigma T \<beta> r \<equiv>
    (\<forall>v<m. 0 < r v \<and>
      B \<le> pheight_rat_log_height (\<beta> v) \<and>
      pheight_rat_log_height (\<beta> v) \<le> xi * T \<and>
      T \<le> real (r v) * pheight_rat_log_height (\<beta> v) \<and>
      real (r v) * pheight_rat_log_height (\<beta> v) \<le> (1 + xi) * T \<and>
      \<bar>of_rat (\<beta> v) - \<alpha>\<bar> \<le>
        exp (- kappa' * pheight_rat_log_height (\<beta> v))) \<and>
    (\<forall>v. Suc v < m \<longrightarrow> real (r (Suc v)) \<le> sigma * real (r v)) \<and>
    real (\<Sum>v<m. r v) \<le> real m * ((1 + xi) * T / B)"

theorem roth_select_parameters:
  assumes inf: "infinite (roth_good_pairs \<alpha> kappa)"
    and kap: "0 < kappa'" "kappa' < kappa"
    and sig: "0 < sigma" and xi: "0 < xi" and Bpos: "0 < B"
  shows "\<exists>\<beta> :: nat \<Rightarrow> rat. \<exists>T r.
    A < (T::real) \<and> 0 < T \<and> roth_selected_parameters \<alpha> kappa' m B xi sigma T \<beta> r"
proof -
  obtain \<beta> :: "nat \<Rightarrow> rat" where \<beta>:
      "\<forall>v<m. B < pheight_rat_log_height (\<beta> v) \<and>
        abs (of_rat (\<beta> v) - \<alpha>) \<le>
          exp (-kappa' * pheight_rat_log_height (\<beta> v))" and growth:
      "\<forall>v. Suc v < m \<longrightarrow>
        (2/sigma) * pheight_rat_log_height (\<beta> v) <
          pheight_rat_log_height (\<beta> (Suc v))"
    using roth_select_near_rationals[where \<alpha>=\<alpha> and kappa=kappa and
      kappa'=kappa' and m=m and B=B and K="2/sigma", OF inf kap]
    by blast
  let ?h = "\<lambda>v. pheight_rat_log_height (\<beta> v)"
  have hlow: "B \<le> ?h v" if vm: "v < m" for v
    using \<beta> vm by auto
  have growth': "2 * ?h v \<le> sigma * ?h (Suc v)"
    if vm: "Suc v < m" for v
  proof -
    have gap: "(2/sigma) * ?h v < ?h (Suc v)"
      using growth vm by blast
    have "((2/sigma) * ?h v) * sigma < ?h (Suc v) * sigma"
      by (rule mult_strict_right_mono[OF gap sig])
    then show ?thesis using sig by (simp add: algebra_simps)
  qed    
  obtain T :: real and r :: "nat \<Rightarrow> nat" where TA: "A < T"
    and Tpos: "0 < T" and rbounds:
      "\<forall>v<m. 0 < r v \<and> B \<le> ?h v \<and> ?h v \<le> xi * T \<and>
        T \<le> real (r v) * ?h v \<and> real (r v) * ?h v \<le> (1+xi)*T"
    and ratio: "\<forall>v. Suc v < m \<longrightarrow>
      real (r (Suc v)) \<le> sigma * real (r v)"
    and sumb: "real (\<Sum>v<m. r v) \<le> real m * ((1+xi)*T/B)"
    using roth_choose_degrees_above[where h="\<lambda>v. pheight_rat_log_height (\<beta> v)" and m=m and sigma=sigma and
      xi=xi and B=B and A=A, OF sig xi Bpos hlow growth'] by blast
  show ?thesis using TA Tpos rbounds \<beta> ratio sumb
    unfolding roth_selected_parameters_def by blast
qed


lemma roth_epsilon_choice:
  fixes kappa :: real
  assumes kap: "2 < kappa"
  defines "eps \<equiv> (kappa - 2) / (6*kappa)"
    and "xi \<equiv> (kappa - 2) / 8"
  shows "0 < eps" "eps < 1" "0 < xi"
    "kappa * ((1-eps)/2 - eps) = 1 + 2*xi"
proof -
  have kpos: "0 < kappa" using kap by linarith
  show "0 < eps" using kap kpos by (simp add: eps_def)
  show "eps < 1" using kap kpos by (simp add: eps_def field_simps)
  show "0 < xi" using kap by (simp add: xi_def)
  show "kappa * ((1-eps)/2 - eps) = 1 + 2*xi"
    using kpos by (simp add: eps_def xi_def field_simps)
qed


lemma roth_choose_m:
  fixes eps :: real and d :: nat
  assumes epos: "0 < eps"
  shows "\<exists>m::nat. 0 < m \<and> 2 * real d < real m * eps\<^sup>2"
proof -
  have sq: "0 < eps\<^sup>2" using epos by simp
  obtain m :: nat where m: "2 * real d / eps\<^sup>2 + 1 < real m"
    using reals_Archimedean2 by blast
  have qnonneg: "0 \<le> 2 * real d / eps\<^sup>2" using sq by simp
  have mrpos: "0 < real m" using m qnonneg by linarith
  have mpos: "0 < m" using mrpos by simp
  have "2 * real d / eps\<^sup>2 < real m" using m by linarith
  then have mult: "(2 * real d / eps\<^sup>2) * eps\<^sup>2 < real m * eps\<^sup>2"
    by (rule mult_strict_right_mono[OF _ sq])
  have gap: "2 * real d < real m * eps\<^sup>2"
    using mult sq by simp
  show ?thesis using mpos gap by blast
qed

lemma roth_numeric_gap:
  fixes T B xi C kappa eps :: real and m S :: nat
  assumes mpos: "0 < m" and Tpos: "0 < T" and Cnonneg: "0 \<le> C"
    and Sbound: "real S \<le> real m * ((1+xi)*T/B)"
    and Bbound: "(1+xi)*C/B \<le> xi/2"
    and Tbound: "ln 2 < real m * T * xi/2"
    and eq: "kappa * ((1-eps)/2 - eps) = 1 + 2*xi"
  shows "ln 2 + real S*C + real m*(1+xi)*T < kappa*T*(real m*(1-eps)/2 - eps*real m)"
proof -
  have "real S*C \<le> real m * ((1+xi)*T/B) * C"
    by (rule mult_right_mono[OF Sbound Cnonneg])
  also have "... = real m*T*((1+xi)*C/B)"
    by (simp add: algebra_simps)
  also have "... \<le> real m*T*(xi/2)"
    by (rule mult_left_mono[OF Bbound]) (use Tpos in simp)
  finally have sc: "real S*C \<le> real m*T*(xi/2)" .
  have "ln 2 + real S*C + real m*(1+xi)*T < real m*T*(1+2*xi)"
    using sc Tbound by (simp add: algebra_simps)
  also have "... = real m*T*(kappa*((1-eps)/2 - eps))"
    using eq by simp
  also have "... = kappa*T*(real m*(1-eps)/2 - eps*real m)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma roth_numeric_height:
  fixes T B xi C sigma :: real and m S r0 :: nat
  assumes Cnonneg: "0 \<le> C"
    and Sbound: "real S \<le> real m * ((1+xi)*T/B)"
    and rbound: "real r0 \<le> (1+xi)*T/B"
    and Bbound: "real m * ((1+xi)*T/B)*(C+4) \<le> sigma*T/2"
    and Tbound: "ln 2 \<le> sigma*T/2"
  shows "ln 2 + real S*C + 4*real m*real r0 \<le> sigma*T"
proof -
  define D where "D = (1+xi)*T/B"
  have Sbound': "real S \<le> real m * D" using Sbound by (simp add: D_def)
  have rbound': "real r0 \<le> D" using rbound by (simp add: D_def)
  have Bbound': "real m * D*(C+4) \<le> sigma*T/2"
    using Bbound by (simp add: D_def)
  have sc: "real S*C \<le> real m*D*C"
    by (rule mult_right_mono[OF Sbound' Cnonneg])
  have rb: "4*real m*real r0 \<le> 4*real m*D"
    using rbound' by (intro mult_left_mono) auto
  have costpre: "ln 2 + real S*C + 4*real m*real r0 \<le> ln 2 + real m*D*C + 4*real m*D"
    using sc rb by linarith
  have costeq: "real m*D*C + 4*real m*D = real m*D*(C+4)"
    by (simp add: algebra_simps)
  show ?thesis using costpre costeq Bbound' Tbound by linarith
qed

lemma roth_height_budget:
  fixes T B xi C sigma :: real and m :: nat
  assumes Tpos: "0 < T"
    and budget: "real m*(1+xi)*(C+4)/B \<le> sigma/2"
  shows "real m*((1+xi)*T/B)*(C+4) \<le> sigma*T/2"
proof -
  have "(real m*(1+xi)*(C+4)/B)*T \<le> (sigma/2)*T"
    by (rule mult_right_mono[OF budget]) (use Tpos in simp)
  then show ?thesis by (simp add: algebra_simps)
qed

lemma roth_choose_budget_denominator:
  fixes a e :: real
  assumes anonneg: "0 \<le> a" and epos: "0 < e"
  shows "\<exists>B::real. 0 < B \<and> a/B < e"
proof -
  let ?B = "a/e + 1"
  have ad: "0 \<le> a/e" 
    using anonneg epos by (intro divide_nonneg_pos) auto
  have eB: "e * ?B = a + e"
    using epos by (simp add: distrib_left)
  have "a < e*?B" using eB epos by linarith
  then have "a/?B < e"
    using ad by (simp add: divide_less_eq mult.commute)
  with ad show ?thesis by (smt (verit, best))
qed

lemma roth_budget_mono:
  fixes a b B :: real
  assumes a: "0 \<le> a" and b: "0 < b" and bB: "b \<le> B"
  shows "a/B \<le> a/b"
proof -
  have "a*b \<le> a*B" by (rule mult_left_mono[OF bB a])
  then show ?thesis using b bB by (simp add: divide_le_eq le_divide_eq)
qed

lemma roth_choose_two_budgets:
  fixes a c e g :: real
  assumes a: "0 \<le> a" and c: "0 \<le> c"
    and e: "0 < e" and g: "0 < g"
  shows "\<exists>B::real. 0 < B \<and> a/B \<le> e \<and> c/B \<le> g"
proof -
  obtain B1 :: real where B1: "0 < B1" "a/B1 < e"
    using roth_choose_budget_denominator[OF a e] by blast
  obtain B2 :: real where B2: "0 < B2" "c/B2 < g"
    using roth_choose_budget_denominator[OF c g] by blast
  let ?B = "max B1 B2"
  have Bpos: "0 < ?B" using B1 by simp
  have aB: "a/?B \<le> a/B1" using roth_budget_mono[OF a B1(1)] by simp
  have cB: "c/?B \<le> c/B2" using roth_budget_mono[OF c B2(1)] by simp
  show ?thesis using Bpos aB cB B1 B2 by (intro exI[of _ ?B]) auto
qed

lemma roth_choose_linear_budgets:
  fixes a c :: real
  assumes apos: "0 < a" and cpos: "0 < c"
  shows "\<exists>A::real. 0 < A \<and> (\<forall>T>A. ln 2 < a*T \<and> ln 2 \<le> c*T)"
proof -
  let ?A = "max (ln 2 / a) (ln 2 / c) + 1"
  have lpos: "0 < ln (2::real)" by simp
  have dnonneg: "0 \<le> ln 2 / a" using lpos apos by simp
  have Apos: "0 < ?A" using dnonneg by simp
  have bound: "ln 2 < a*T \<and> ln 2 \<le> c*T" if TA: "?A < T" for T
  proof -
    have aa: "ln 2 / a < T" using TA by linarith
    have cc: "ln 2 / c < T" using TA by linarith
    have al: "(ln 2 / a)*a < T*a"
      by (rule mult_strict_right_mono[OF aa apos])
    have cl: "(ln 2 / c)*c < T*c"
      by (rule mult_strict_right_mono[OF cc cpos])
    show ?thesis using al cl apos cpos by (simp add: mult.commute)
  qed
  show ?thesis using Apos bound by blast
qed

lemma roth_auxiliary_bound_log:
  fixes b :: int and S :: nat
  assumes bpos: "1 \<le> b"
  shows "ln (real (nat (2 * (4*b)^S))) = ln 2 + real S * ln (4 * real_of_int b)"
  using bpos by (simp add: ln_mult ln_realpow algebra_simps)

lemma roth_degree_from_weighted:
  fixes T B xi h :: real and r :: nat
  assumes Bpos: "0 < B" and Bh: "B \<le> h"
    and weighted: "real r * h \<le> (1+xi)*T"
  shows "real r \<le> (1+xi)*T/B"
proof -
  have "real r * B \<le> real r * h"
    by (rule mult_left_mono[OF Bh]) simp
  then show ?thesis using weighted Bpos by (simp add: le_divide_eq)
qed

lemma roth_choose_parameter_budget:
  fixes xi sigma C D :: real and m :: nat
  assumes xi: "0 < xi" and sig: "0 < sigma"
    and C: "0 \<le> C" and D: "0 \<le> D"
  shows "\<exists>B::real. 0 < B \<and> (1+xi)*(C+D)/B \<le> xi/2 \<and> real m*(1+xi)*(C+4)/B \<le> sigma/2"
proof -
  have a: "0 \<le> (1+xi)*(C+D)" using xi C D by simp
  have c: "0 \<le> real m*(1+xi)*(C+4)" using xi C by simp
  show ?thesis
    using roth_choose_two_budgets[OF a c, of "xi/2" "sigma/2"] xi sig by simp
qed

end
