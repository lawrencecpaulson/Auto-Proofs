theory Roth_Approximant_Selection
  imports Roth_Conditional_Contradiction
begin

lemma roth_good_pairs_unbounded_height:
  assumes inf: "infinite (roth_good_pairs alpha kappa)"
  shows "\<forall>N::nat. \<exists>p q. (p,q) \<in> roth_good_pairs alpha kappa \<and>
    N < roth_rat_height (Rat.Fract p q)"
proof
  fix N :: nat
  obtain pq where mem: "pq \<in> roth_good_pairs alpha kappa"
    and qlarge: "int N < snd pq"
    using infinite_roth_good_pairs_iff_unbounded_denominator[of alpha kappa]
      inf by blast
  obtain p q where pq: "pq = (p,q)" by (cases pq) auto
  have good: "(p,q) \<in> roth_good_pairs alpha kappa" using mem pq by simp
  have qpos: "0 < q" and cop: "coprime p q" using good by auto
  have height: "roth_rat_height (Rat.Fract p q) = nat (max (abs p) q)"
    using qpos cop by (simp add: roth_rat_height_Fract)
  have "N < nat q" using qlarge pq by simp
  also have "... \<le> roth_rat_height (Rat.Fract p q)"
    by (simp add: height)
  finally show "\<exists>p q. (p,q) \<in> roth_good_pairs alpha kappa \<and>
      N < roth_rat_height (Rat.Fract p q)"
    using good by blast
qed

lemma roth_good_pairs_unbounded_log_height:
  assumes inf: "infinite (roth_good_pairs alpha kappa)"
  shows "\<forall>B::real. \<exists>p q. (p,q) \<in> roth_good_pairs alpha kappa \<and>
    B < roth_rat_log_height (Rat.Fract p q)"
proof
  fix B :: real
  obtain N :: nat where N: "exp B < real N"
    using reals_Archimedean2 by blast
  obtain p q where good: "(p,q) \<in> roth_good_pairs alpha kappa"
    and height: "N < roth_rat_height (Rat.Fract p q)"
    using roth_good_pairs_unbounded_height[OF inf, rule_format, of N] by blast
  have "exp B < real (roth_rat_height (Rat.Fract p q))"
    using N height by simp
  then have "ln (exp B) < ln (real (roth_rat_height (Rat.Fract p q)))"
    by (intro ln_strict_mono) simp_all
  then show "\<exists>p q. (p,q) \<in> roth_good_pairs alpha kappa \<and>
    B < roth_rat_log_height (Rat.Fract p q)"
    using good by (auto simp: roth_rat_log_height_def)
qed

lemma roth_unbounded_sequence:
  fixes S :: "'a set" and h :: "'a \<Rightarrow> real"
  assumes unbounded: "\<And>B. \<exists>x\<in>S. B < h x"
  shows "\<exists>xs :: nat \<Rightarrow> 'a.
    (\<forall>v<m. xs v \<in> S \<and> B < h (xs v)) \<and>
    (\<forall>v. Suc v < m \<longrightarrow> K * h (xs v) < h (xs (Suc v)))"
proof (induct m)
  case 0
  obtain x where xS: "x \<in> S" using unbounded[of B] by blast
  show ?case by (intro exI[of _ "\<lambda>_. x"]) simp
next
  case (Suc m)
  obtain xs :: "nat \<Rightarrow> 'a" where old:
      "\<forall>v<m. xs v \<in> S \<and> B < h (xs v)" and growth:
      "\<forall>v. Suc v < m \<longrightarrow> K * h (xs v) < h (xs (Suc v))"
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

theorem roth_select_good_pairs:
  assumes inf: "infinite (roth_good_pairs alpha kappa)"
  shows "\<exists>pq :: nat \<Rightarrow> int \<times> int.
    (\<forall>v<m. pq v \<in> roth_good_pairs alpha kappa \<and>
      B < roth_rat_log_height (Rat.Fract (fst (pq v)) (snd (pq v)))) \<and>
    (\<forall>v. Suc v < m \<longrightarrow>
      K * roth_rat_log_height (Rat.Fract (fst (pq v)) (snd (pq v))) <
      roth_rat_log_height (Rat.Fract (fst (pq (Suc v))) (snd (pq (Suc v)))))"
proof -
  let ?h = "\<lambda>pq. roth_rat_log_height (Rat.Fract (fst pq) (snd pq))"
  have unb: "\<And>C. \<exists>pq\<in>roth_good_pairs alpha kappa. C < ?h pq"
  proof -
    fix C :: real
    obtain p q where good: "(p,q) \<in> roth_good_pairs alpha kappa"
      and big: "C < roth_rat_log_height (Rat.Fract p q)"
      using roth_good_pairs_unbounded_log_height[OF inf, rule_format, of C] by blast
    show "\<exists>pq\<in>roth_good_pairs alpha kappa. C < ?h pq"
      using good big by (metis fst_conv snd_conv)
  qed
  show ?thesis using roth_unbounded_sequence[OF unb, of m B K] by simp
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
  have lo: "?z \<le> real (roth_rounded_degrees T h v)"
    using real_eq by simp
  show "T \<le> real (roth_rounded_degrees T h v) * h v"
    using lo hpos by (simp add: divide_le_eq)
  have hi: "real (roth_rounded_degrees T h v) \<le> ?z + 1"
    using real_eq by simp
  have "real (roth_rounded_degrees T h v) * h v \<le> (?z + 1) * h v"
    using hi hpos by (intro mult_right_mono) auto
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
  have upper: "real (roth_rounded_degrees T h (Suc v)) \<le>
      T / h (Suc v) + 1"
    using Tpos hpos(2) by (simp add: roth_rounded_degrees_def)
  have lower: "T / h v \<le> real (roth_rounded_degrees T h v)"
    using roth_rounded_degrees_bounds(2)[of T h v] Tpos hpos(1)
    by (simp add: divide_le_eq)
  have "sigma * (T / h v) \<le>
      sigma * real (roth_rounded_degrees T h v)"
    by (rule mult_left_mono[OF lower sig])
  then show ?thesis using upper gap by linarith
qed

end
