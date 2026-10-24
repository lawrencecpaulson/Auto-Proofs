theory Roth_Parameter_Bounds
  imports Roth_Degree_Selection
begin

lemma roth_choose_large_T_above:
  fixes h :: "nat \<Rightarrow> real"
  assumes sig: "0 < sigma"
  shows "\<exists>T::real. A < T \<and> 0 < T \<and>
    (\<forall>v<m. 2 * h v \<le> sigma * T)"
proof -
  obtain T0 :: real where T0pos: "0 < T0" and bound0:
      "\<forall>v<m. 2 * h v \<le> sigma * T0"
    using roth_choose_large_T[where h=h and m=m, OF sig] by blast
  let ?T = "T0 + max A 0 + 1"
  have Tpos: "0 < ?T" and TA: "A < ?T"
    using T0pos by auto
  have b: "2 * h v \<le> sigma * ?T" if vm: "v < m" for v
  proof -
    have h: "2 * h v \<le> sigma * T0" using bound0 vm by blast
    have le: "sigma * T0 \<le> sigma * ?T"
      using sig by (intro mult_left_mono) auto
    show ?thesis using h le by linarith
  qed
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
  have lo: "T \<le> real (roth_rounded_degrees T h v) * h v"
    using roth_rounded_degrees_bounds(2)[of T h v] Tpos hpos by simp
  have hi: "real (roth_rounded_degrees T h v) * h v \<le> T + h v"
    using roth_rounded_degrees_bounds(3)[of T h v] Tpos hpos by simp
  have w: "real (roth_rounded_degrees T h v) * h v \<le> (1+xi)*T"
    using hi hbound by (simp add: algebra_simps)
  have B_le: "real (roth_rounded_degrees T h v) * B \<le>
      real (roth_rounded_degrees T h v) * h v"
    using hbound by (intro mult_left_mono) auto
  show "T \<le> real (roth_rounded_degrees T h v) * h v" using lo .
  show "real (roth_rounded_degrees T h v) * h v \<le> (1+xi)*T" using w .
  show "real (roth_rounded_degrees T h v) \<le> (1+xi)*T/B"
    using B_le w Bpos by (simp add: le_divide_eq)
qed

lemma roth_degree_sum:
  fixes h :: "nat \<Rightarrow> real"
  assumes Tpos: "0 < T" and Bpos: "0 < B" and xipos: "0 \<le> xi"
    and hbound: "\<And>v. v < m \<Longrightarrow> B \<le> h v \<and> h v \<le> xi * T"
  shows "real (\<Sum>v<m. roth_rounded_degrees T h v) \<le>
    real m * ((1+xi)*T/B)"
proof -
  have each: "real (roth_rounded_degrees T h v) \<le> (1+xi)*T/B"
    if vm: "v < m" for v
    using roth_degree_uniform(3)[of T B xi h v] Tpos Bpos xipos
      hbound[OF vm] by auto
  have "(\<Sum>v<m. real (roth_rounded_degrees T h v)) \<le>
      (\<Sum>v<m. (1+xi)*T/B)"
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
  have Mnonneg: "0 \<le> ?M" by (rule Max_ge) simp_all
  have hle: "h v \<le> ?M" if vm: "v < m" for v
    by (rule Max_ge) (use vm in auto)
  obtain T :: real where Tbig: "max A (?M/xi) < T" and Tpos: "0 < T"
    and large: "\<And>v. v < m \<Longrightarrow> 2 * h v \<le> sigma * T"
    using roth_choose_large_T_above[where h=h and m=m and A="max A (?M/xi)", OF sig]
    by blast
  have TA: "A < T" using Tbig by simp
  have div: "?M / xi < T" using Tbig by simp
  have cross: "(?M / xi) * xi < T * xi"
    by (rule mult_strict_right_mono[OF div xi])
  have cancel: "(?M / xi) * xi = ?M" using xi by simp
  have MT: "?M < xi * T"
    using cross cancel by (simp only: mult.commute)
  have hsmall: "h v \<le> xi * T" if vm: "v < m" for v
    using hle[OF vm] MT by linarith
  let ?r = "roth_rounded_degrees T h"
  have hpos: "0 < h v" if vm: "v < m" for v
    using hlow[OF vm] Bpos by linarith
  have bounds: "\<forall>v<m. 0 < ?r v \<and> B \<le> h v \<and> h v \<le> xi * T \<and>
      T \<le> real (?r v) * h v \<and> real (?r v) * h v \<le> (1+xi)*T"
  proof (intro allI impI conjI)
    fix v
    assume vm: "v < m"
    have hv: "0 < h v" by (rule hpos[OF vm])
    show "0 < ?r v" using roth_rounded_degrees_bounds(1)[of T h v] Tpos hv by simp
    show "B \<le> h v" by (rule hlow[OF vm])
    show "h v \<le> xi * T" by (rule hsmall[OF vm])
    show "T \<le> real (?r v) * h v"
      using roth_rounded_degrees_bounds(2)[of T h v] Tpos hv by simp
    show "real (?r v) * h v \<le> (1+xi)*T"
      using roth_degree_uniform(2)[of T B xi h v] Tpos Bpos xi hlow[OF vm]
        hsmall[OF vm] by simp
  qed
  have ratios: "\<forall>v. Suc v < m \<longrightarrow>
      real (?r (Suc v)) \<le> sigma * real (?r v)"
    using roth_rounded_degrees_ratios[where T=T and sigma=sigma and h=h and m=m]
      Tpos sig hpos growth large by blast
  have sumb: "real (\<Sum>v<m. ?r v) \<le> real m * ((1+xi)*T/B)"
    by (rule roth_degree_sum[OF Tpos Bpos _])
      (use hlow hsmall xi in auto)
  show ?thesis using TA Tpos bounds ratios sumb by blast
qed


theorem roth_select_parameters:
  assumes inf: "infinite (roth_good_pairs alpha kappa)"
    and kap: "0 < kappa'" "kappa' < kappa"
    and sig: "0 < sigma" and xi: "0 < xi" and Bpos: "0 < B"
  shows "\<exists>beta :: nat \<Rightarrow> rat. \<exists>T r.
    A < (T::real) \<and> 0 < T \<and>
    (\<forall>v<m. 0 < r v \<and>
      B \<le> roth_rat_log_height (beta v) \<and>
      roth_rat_log_height (beta v) \<le> xi * T \<and>
      T \<le> real (r v) * roth_rat_log_height (beta v) \<and>
      real (r v) * roth_rat_log_height (beta v) \<le> (1+xi)*T \<and>
      abs (of_rat (beta v) - alpha) \<le>
        exp (-kappa' * roth_rat_log_height (beta v))) \<and>
    (\<forall>v. Suc v < m \<longrightarrow> real (r (Suc v)) \<le> sigma * real (r v)) \<and>
    real (\<Sum>v<m. r v) \<le> real m * ((1+xi)*T/B)"
proof -
  obtain beta :: "nat \<Rightarrow> rat" where beta:
      "\<forall>v<m. B < roth_rat_log_height (beta v) \<and>
        abs (of_rat (beta v) - alpha) \<le>
          exp (-kappa' * roth_rat_log_height (beta v))" and growth:
      "\<forall>v. Suc v < m \<longrightarrow>
        (2/sigma) * roth_rat_log_height (beta v) <
          roth_rat_log_height (beta (Suc v))"
    using roth_select_near_rationals[where alpha=alpha and kappa=kappa and
      kappa'=kappa' and m=m and B=B and K="2/sigma", OF inf kap]
    by blast
  let ?h = "\<lambda>v. roth_rat_log_height (beta v)"
  have hlow: "B \<le> ?h v" if vm: "v < m" for v
    using beta vm by auto
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
    using roth_choose_degrees_above[where h="\<lambda>v. roth_rat_log_height (beta v)" and m=m and sigma=sigma and
      xi=xi and B=B and A=A, OF sig xi Bpos hlow growth'] by blast
  have all: "\<forall>v<m. 0 < r v \<and> B \<le> ?h v \<and> ?h v \<le> xi * T \<and>
      T \<le> real (r v) * ?h v \<and> real (r v) * ?h v \<le> (1+xi)*T \<and>
      abs (of_rat (beta v) - alpha) \<le> exp (-kappa' * ?h v)"
    using rbounds beta by blast
  show ?thesis using TA Tpos all ratio sumb by blast
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

end
