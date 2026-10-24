theory Roth_Parameter_Costs
  imports Roth_Parameter_Bounds
begin

lemma roth_numeric_gap:
  fixes T B xi C kappa eps :: real and m S :: nat
  assumes mpos: "0 < m" and Tpos: "0 < T" and Cnonneg: "0 \<le> C"
    and Sbound: "real S \<le> real m * ((1+xi)*T/B)"
    and Bbound: "(1+xi)*C/B \<le> xi/2"
    and Tbound: "ln 2 < real m * T * xi/2"
    and eq: "kappa * ((1-eps)/2 - eps) = 1 + 2*xi"
  shows "ln 2 + real S*C + real m*(1+xi)*T <
    kappa*T*(real m*(1-eps)/2 - eps*real m)"
proof -
  have mTnonneg: "0 \<le> real m * T" using Tpos by simp
  have sc0: "real S*C \<le> (real m * ((1+xi)*T/B))*C"
    by (rule mult_right_mono[OF Sbound Cnonneg])
  have sc: "real S*C \<le> real m*T*((1+xi)*C/B)"
    using sc0 by (simp add: algebra_simps)
  have bc: "real m*T*((1+xi)*C/B) \<le> real m*T*(xi/2)"
    by (rule mult_left_mono[OF Bbound mTnonneg])
  have scb: "real S*C \<le> real m*T*(xi/2)"
    using sc bc by linarith
  have lnB: "ln 2 < real m*T*(xi/2)"
    using Tbound by (simp add: algebra_simps)
  have cost: "ln 2 + real S*C + real m*(1+xi)*T <
      real m*T*(xi/2) + real m*T*(xi/2) + real m*(1+xi)*T"
    using scb lnB by linarith
  have delta: "real m*(1-eps)/2 - eps*real m =
      real m*((1-eps)/2 - eps)" by (simp add: algebra_simps)
  have form1: "real m*T*(xi/2) + real m*T*(xi/2) + real m*(1+xi)*T =
      real m*T*(1+2*xi)" by (simp add: algebra_simps)
  have form2: "real m*T*(1+2*xi) =
      kappa*T*(real m*(1-eps)/2 - eps*real m)"
    using eq by (simp add: delta mult_ac)
  have form: "real m*T*(xi/2) + real m*T*(xi/2) + real m*(1+xi)*T =
      kappa*T*(real m*(1-eps)/2 - eps*real m)"
    using form1 form2 by simp
  show ?thesis using cost form by simp
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
  have costpre: "ln 2 + real S*C + 4*real m*real r0 \<le>
      ln 2 + real m*D*C + 4*real m*D"
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
  have eq: "real m*((1+xi)*T/B)*(C+4) =
      (real m*(1+xi)*(C+4)/B)*T"
    by (simp add: algebra_simps)
  have "(real m*(1+xi)*(C+4)/B)*T \<le> (sigma/2)*T"
    by (rule mult_right_mono[OF budget]) (use Tpos in simp)
  then show ?thesis using eq by (simp add: algebra_simps)
qed

lemma roth_choose_budget_denominator:
  fixes a e :: real
  assumes anonneg: "0 \<le> a" and epos: "0 < e"
  shows "\<exists>B::real. 0 < B \<and> a/B < e"
proof -
  let ?B = "a/e + 1"
  have ad: "0 \<le> a/e" using anonneg epos by (intro divide_nonneg_pos) auto
  have Bpos: "0 < ?B" using ad by linarith
  have eB: "e * ?B = a + e"
    using epos by (simp add: distrib_left)
  have "a < e*?B" using eB epos by linarith
  then have bound: "a/?B < e"
    using Bpos by (simp add: divide_less_eq mult.commute)
  show ?thesis using Bpos bound by blast
qed

lemma roth_budget_mono:
  fixes a b B :: real
  assumes a: "0 \<le> a" and b: "0 < b" and bB: "b \<le> B"
  shows "a/B \<le> a/b"
proof -
  have Bpos: "0 < B" using b bB by linarith
  have "a*b \<le> a*B" by (rule mult_left_mono[OF bB a])
  then show ?thesis using b Bpos by (simp add: divide_le_eq le_divide_eq)
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
  shows "ln (real (nat (2 * (4*b)^S))) =
    ln 2 + real S * ln (4 * real_of_int b)"
proof -
  have nonneg: "0 \<le> 2 * (4*b)^S" using bpos by simp
  have eq: "real (nat (2 * (4*b)^S)) = 2 * (4 * real_of_int b)^S"
    using nonneg by simp
  show ?thesis using bpos by (simp add: eq ln_mult ln_realpow algebra_simps)
qed

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
  shows "\<exists>B::real. 0 < B \<and>
    (1+xi)*(C+D)/B \<le> xi/2 \<and>
    real m*(1+xi)*(C+4)/B \<le> sigma/2"
proof -
  have a: "0 \<le> (1+xi)*(C+D)" using xi C D by simp
  have c: "0 \<le> real m*(1+xi)*(C+4)" using xi C by simp
  show ?thesis
    using roth_choose_two_budgets[OF a c, of "xi/2" "sigma/2"] xi sig by simp
qed

end
