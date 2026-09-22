(*  Title:      NSA_Worked_Examples.thy
    Author:     OpenAI Codex

A small ladder of worked examples illustrating the nonstandard-analysis
viewpoint: infinite hypernumbers, infinitesimals, nonstandard limits,
and direct infinitesimal proofs of continuity and differentiation.
*)

theory NSA_Worked_Examples
  imports "HOL-Nonstandard_Analysis.Nonstandard_Analysis"
begin

section \<open>Worked Examples in Nonstandard Analysis\<close>

text \<open>
The first examples are basic algebra with infinite and infinitesimal
quantities. They are already present in the library, but it is useful to
see them isolated as a starter kit.
\<close>

subsection \<open>Infinite and Infinitesimal Quantities\<close>

lemma example_infinite_inverse_infinitesimal:
  assumes "x \<in> HInfinite"
  shows "inverse (x :: hypreal) \<in> Infinitesimal"
  using assms by (rule HInfinite_inverse_Infinitesimal)

lemma example_sum_of_infinitesimals:
  assumes "e \<in> Infinitesimal" and "d \<in> Infinitesimal"
  shows "e + d \<in> Infinitesimal"
  using assms by (rule Infinitesimal_add)

lemma example_finite_times_infinitesimal:
  assumes "u \<in> HFinite" and "e \<in> Infinitesimal"
  shows "(u :: hypreal) * e \<in> Infinitesimal"
  using assms by (simp add: mult.commute Infinitesimal_HFinite_mult)

lemma example_same_standard_part:
  assumes "x \<in> HFinite" and "y \<in> HFinite" and "x \<approx> y"
  shows "st (x :: hypreal) = st y"
  using assms by (simp add: st_eq_approx_iff)

lemma example_standard_part_decomposition:
  assumes "x \<in> HFinite"
  shows "\<exists>e \<in> Infinitesimal. (x :: hypreal) = st x + e"
  using assms by (rule HFinite_st_Infinitesimal_add)


subsection \<open>Sequence Limits\<close>

text \<open>
The nonstandard criterion for convergence replaces an eventual
epsilon-argument by the single requirement that every infinite index
produces a term infinitely close to the proposed limit.
\<close>

lemma example_inverse_nat_nslim:
  "(\<lambda>n. inverse (real (Suc n))) \<longlonglongrightarrow>\<^sub>N\<^sub>S (0::real)"
  by (rule NSLIMSEQ_inverse_real_of_nat)

lemma example_inverse_nat_nslim_direct:
  "(\<lambda>n. inverse (real (Suc n))) \<longlonglongrightarrow>\<^sub>N\<^sub>S (0::real)"
proof (rule NSLIMSEQ_I)
  fix N :: hypnat
  assume N: "N \<in> HNatInfinite"
  have N1: "N + 1 \<in> HNatInfinite"
    using N by (rule HNatInfinite_add)
  have star_inverse:
    "( *f* (\<lambda>n. inverse (real (Suc n)))) N = inverse (1 + hypreal_of_hypnat N)"
    by (simp add: starfun_shift_one starfunNat_real_of_nat starfun_inverse_real_of_nat_eq[OF N1])
  have "inverse (1 + hypreal_of_hypnat N) \<in> Infinitesimal"
    using HNatInfinite_inverse_Infinitesimal[OF N1] by (simp add: add.commute)
  with star_inverse show "( *f* (\<lambda>n. inverse (real (Suc n)))) N \<approx> star_of (0::real)"
    by (simp add: approx_def)
qed

lemma example_geometric_nslim:
  assumes "\<bar>c\<bar> < 1"
  shows "(\<lambda>n. c ^ n) \<longlonglongrightarrow>\<^sub>N\<^sub>S (0::real)"
  using assms by (rule NSLIMSEQ_abs_realpow_zero2)

theorem example_nonstandard_cauchy_criterion:
  "NSCauchy X \<longleftrightarrow> Cauchy X"
  by (rule NSCauchy_Cauchy_iff)

lemma example_sin_small_angle_nslim:
  "(\<lambda>n. real (Suc n) * sin (inverse (real (Suc n)))) \<longlonglongrightarrow>\<^sub>N\<^sub>S (1::real)"
proof (rule NSLIMSEQ_I)
  fix N :: hypnat
  assume N: "N \<in> HNatInfinite"
  have N1: "N + 1 \<in> HNatInfinite"
    using N by (rule HNatInfinite_add)
  have star_seq:
    "( *f* (\<lambda>n. real (Suc n) * sin (inverse (real (Suc n))))) N =
      hypreal_of_hypnat (N + 1) * ( *f* sin) (inverse (hypreal_of_hypnat (N + 1)))"
  proof -
    have "( *f* (\<lambda>n. real (Suc n) * sin (inverse (real (Suc n))))) N =
        ( *f* (\<lambda>n. real n * sin (inverse (real n)))) (N + 1)"
      by (rule starfun_shift_one)
    also have "... =
        hypreal_of_hypnat (N + 1) *
        ( *f* (\<lambda>n. sin (inverse (real n)))) (N + 1)"
      by (simp add: starfunNat_real_of_nat)
    also have "... =
        hypreal_of_hypnat (N + 1) *
        ( *f* sin) (( *f* (\<lambda>n. inverse (real n))) (N + 1))"
    proof -
      have "( *f* (\<lambda>n. sin (inverse (real n)))) (N + 1) =
          ( *f* sin) (( *f* (\<lambda>n. inverse (real n))) (N + 1))"
        using fun_cong[OF starfun_o2[of sin "\<lambda>n. inverse (real n)"], of "N + 1"] by simp
      then show ?thesis
        by simp
    qed
    also have "... =
        hypreal_of_hypnat (N + 1) * ( *f* sin) (inverse (hypreal_of_hypnat (N + 1)))"
      using starfun_inverse_real_of_nat_eq[OF N1] by simp
    finally show ?thesis .
  qed
  have "( *f* sin) (inverse (hypreal_of_hypnat (N + 1))) * hypreal_of_hypnat (N + 1) \<approx> (1::hypreal)"
    using STAR_sin_inverse_HNatInfinite[OF N1] .
  then have "hypreal_of_hypnat (N + 1) * ( *f* sin) (inverse (hypreal_of_hypnat (N + 1))) \<approx> star_of (1::real)"
    by (simp add: mult.commute)
  with star_seq show
    "( *f* (\<lambda>n. real (Suc n) * sin (inverse (real (Suc n))))) N \<approx> star_of (1::real)"
    by simp
qed


subsection \<open>Infinitesimal Function Behavior\<close>

text \<open>
These are typical ``small input gives small change'' statements in the
nonstandard idiom.
\<close>

lemma example_sine_of_infinitesimal:
  assumes "h \<in> Infinitesimal"
  shows "( *f* sin) (h :: hypreal) \<approx> h"
  using assms by (rule STAR_sin_Infinitesimal)

lemma example_exp_of_infinitesimal:
  assumes "h \<in> Infinitesimal"
  shows "( *f* exp) h \<approx> (1::hypreal)"
  using assms by (rule STAR_exp_Infinitesimal)


subsection \<open>Continuity Examples\<close>

text \<open>
Continuity can be read off from the nonstandard derivative rules, while the
more instructive long proofs below are the small-angle sequence limit and the
direct derivative calculation for the reciprocal function.
\<close>

lemma example_nscont_square_direct:
  "isNSCont (\<lambda>x::real. x\<^sup>2) x"
  using NSDERIV_pow[of 2 x] by (simp add: NSDERIV_isNSCont)

lemma example_nscont_inverse_direct:
  assumes "x \<noteq> (0::real)"
  shows "isNSCont (\<lambda>t. inverse t) x"
  by (rule isNSCont_inverse[where f = "\<lambda>t::real. t"]) (simp_all add: assms isNSCont_def)


subsection \<open>A Direct Infinitesimal Derivative Proof\<close>

text \<open>
For the square function the difference quotient collapses immediately:
\[
  \frac{(x+h)^2 - x^2}{h} = 2x + h.
\]
If \<open>h\<close> is infinitesimal, then this is infinitely close to \<open>2x\<close>.
\<close>

lemma example_square_difference_quotient:
  assumes "h \<noteq> 0"
  shows
    "((( *f* (\<lambda>t::real. t\<^sup>2)) (star_of x + h)) - star_of (x\<^sup>2)) / h =
      star_of (2 * x) + h"
  using assms by (simp add: power2_eq_square field_simps algebra_simps)

lemma example_nsderiv_square:
  "NSDERIV (\<lambda>x::real. x\<^sup>2) x :> 2 * x"
  using NSDERIV_pow[of 2 x] by simp

lemma example_nsderiv_inverse_direct:
  assumes "x \<noteq> (0::real)"
  shows "NSDERIV (\<lambda>t. inverse t) x :> - inverse (x\<^sup>2)"
proof -
  {
    fix h :: hypreal
    assume h_inf: "h \<in> Infinitesimal"
    assume h0: "h \<noteq> 0"
    from h_inf assms have xh0: "star_of x + h \<noteq> 0"
      by (rule Infinitesimal_add_not_zero)
    from h_inf have hx_inf: "h * star_of x \<in> Infinitesimal"
      by (rule Infinitesimal_HFinite_mult) simp
    have inv_approx:
      "inverse (- (h * star_of x) + - (star_of x * star_of x)) \<approx>
        inverse (- (star_of x * star_of x))"
    proof -
      have neg_hx_inf: "- (h * star_of x) \<in> Infinitesimal"
        using hx_inf by simp
      have "- (star_of x * star_of x) \<approx> - (h * star_of x) + - (star_of x * star_of x)"
        using neg_hx_inf by (rule Infinitesimal_add_approx_self2)
      then have "- (h * star_of x) + - (star_of x * star_of x) \<approx> - (star_of x * star_of x)"
        by (rule approx_sym)
      then show ?thesis
        by (metis assms mult_eq_0_iff neg_equal_0_iff_equal star_of_approx_inverse star_of_minus star_of_mult)
    qed
    moreover have "inverse (- (h * star_of x) + - (star_of x * star_of x)) =
      (inverse (star_of x + h) - inverse (star_of x)) / h"
      using xh0 h0 assms
      by (simp add: division_ring_inverse_diff inverse_mult_distrib [symmetric]
          inverse_minus_eq [symmetric] algebra_simps)
    ultimately have "(inverse (star_of x + h) - inverse (star_of x)) / h \<approx>
      - (inverse (star_of x) * inverse (star_of x))"
      using assms by simp
  }
  then show ?thesis
    by (simp add: nsderiv_def power2_eq_square)
qed

lemma example_nscont_square:
  "isNSCont (\<lambda>x::real. x\<^sup>2) x"
  using example_nsderiv_square by (rule NSDERIV_isNSCont)

end
