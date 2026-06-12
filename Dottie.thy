section \<open>The Dottie Number\<close>

theory Dottie
  imports "HOL-Analysis.Analysis"
          "HOL-Decision_Procs.Approximation"

begin

text \<open>
  The Dottie number, approximately 0.739085133215, 
  is the unique fixed point of the cosine function.
\<close>

definition dottie :: real where
  "dottie \<equiv> THE x. cos x = x"

lemma cos_1_lt_1: "cos (1::real) < 1"
  using cos_monotone_0_pi pi_gt3 by force

text \<open>We shall reason about the function $g(x) = \cos x - x$.
The locale provides a scope for $g$ and its
properties, which are used by several of the lemmas below.\<close>

locale Dottie =
  fixes g :: "real \<Rightarrow> real"
  defines "g \<equiv> \<lambda>x::real. cos x - x"

begin

lemma g_has_negative_deriv:
  assumes "\<bar>t\<bar> \<le> 1" 
  shows "\<exists>d. (g has_real_derivative d) (at t) \<and> d < 0"
proof (intro exI conjI)
  show "(g has_real_derivative (- sin t - 1)) (at t)"
    unfolding g_def by (auto intro!: derivative_eq_intros)
  show "- sin t - 1 < 0"
    using assms pi_gt3 le_arcsin_iff [of _ t] by fastforce
qed

subsection \<open>Existence\<close>

text \<open>We have $g(0) = 1 > 0$ and $g(1) = \cos 1 - 1 < 0$.
  Since $g$ is continuous, the intermediate value theorem gives
  a point $x \in (0, 1)$ where $g(x) = 0$, i.e.\ $\cos x = x$.\<close>

lemma dottie_exists: "\<exists>x::real. 0 < x \<and> x < 1 \<and> cos x = x"
proof -
  \<comment> \<open>Apply the IVT to @{term g} on the unit interval at 0.\<close>
  have g_cont: "continuous_on {0..1} g"
    unfolding g_def by (intro continuous_intros)
  obtain "g 0 = 1" "g 1 < 0" using cos_1_lt_1 by (simp add: g_def)
  with IVT2'[of g 1 0 0] g_cont
  obtain x where hx: "0 \<le> x" "x \<le> 1" "g x = 0"
    by (metis less_eq_real_def zero_le_one)
  hence cos_eq: "cos x = x" by (simp add: g_def)
  with hx show ?thesis
    by (metis cos_1_lt_1 cos_zero order_less_le)
qed

subsection \<open>Uniqueness\<close>

text \<open>The function $g(x) = \cos x - x$ has derivative
  $g'(x) = -\sin x - 1$, which is strictly negative for $x \in [-1,1]$
  (since $\sin x \ge 0$ there).  A function with strictly negative derivative
  is strictly decreasing, so $g$ can have at most one zero. 
  We can extend uniqueness to the entire real line.\<close>

lemma dottie_unique:
  fixes x y :: real
  assumes "cos x = x" "cos y = y"
  shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  have gx: "g x = 0" and gy: "g y = 0" using assms by (auto simp: g_def)
  \<comment> \<open>The derivative of @{term g} is @{term "\<lambda>x. - sin x - 1"}, which is negative on @{term "{-1..1}"}.\<close>
  show False
  proof (cases "\<bar>x\<bar> > 1 \<or> \<bar>y\<bar> > 1")
    case True
    then show ?thesis
      by (metis assms abs_cos_le_one not_less)
  next
    case False
    then have "\<bar>x\<bar> \<le> 1 \<and> \<bar>y\<bar> \<le> 1"
      by simp
    moreover have "x < y \<or> y < x" using \<open>x \<noteq> y\<close> by linarith
    ultimately show ?thesis
      using DERIV_neg_imp_decreasing [OF _ g_has_negative_deriv] gx gy
      by force
  qed
qed

lemma facts: "0 < dottie" "dottie < 1" "cos dottie = dottie" 
proof -
  obtain x :: real where hx: "0 < x" "x < 1" "cos x = x"
    using dottie_exists by blast
  have unique: "y = x" if "cos y = y" for y :: real
    by (simp add: dottie_unique \<open>cos x = x\<close> that)
  have the_eq: "dottie = x"
    unfolding dottie_def using \<open>cos x = x\<close> unique by blast
  then show "0 < dottie" "dottie < 1" "cos dottie = dottie" 
    using hx by (auto simp: g_def)
qed

subsection \<open>Approximation\<close>

text \<open>We pin down the Dottie number to 12 decimal
  places. Note that $g$ is decreasing. We check that
  $\cos(lb) > lb$ (so the fixed point is above $lb$) and
  $\cos(ub) < u$ (so it is below $ub$).\<close>

definition lb::real where "lb \<equiv> 0.739085133215"

definition ub::real where "ub \<equiv> 0.739085133216"

lemma lb_gt: "cos lb > lb"
  unfolding lb_def
  by (approximation 50)

lemma ub_lt: "cos ub < ub"
  unfolding ub_def
  by (approximation 50)

lemma lb: "lb < dottie"
proof (rule ccontr)
  assume neg: "\<not> lb < dottie"
  have gd: "g lb > 0" 
    using facts lb_gt by (auto simp: g_def)
  show False
    using DERIV_neg_imp_decreasing [OF _ g_has_negative_deriv] facts neg
    by (smt (verit, ccfv_SIG) cos_le_one cos_monotone_0_pi lb_gt pi_gt3)
qed

lemma ub: "ub > dottie"
proof (rule ccontr)
  assume neg: "\<not> ub > dottie"
  have gd: "g ub < 0" 
    using facts ub_lt by (auto simp: g_def)
  show False
    using DERIV_neg_imp_decreasing [OF _ g_has_negative_deriv] facts neg
    by (smt (verit) cos_ge_minus_one ub_lt gd g_def)
qed

end

text \<open> We make key facts available outside the locale \<close>
lemmas dottie_fp = Dottie.facts(3)
lemmas dottie_bounds = Dottie.lb Dottie.ub

end



