theory Math_Examples
  imports "HOL-Analysis.Analysis"
          "HOL-Decision_Procs.Approximation"

begin
section \<open>The Irrationality of $\sqrt{2}$\<close>

text \<open>
  One of the most celebrated results in mathematics, dating back to ancient Greece,
  is that $\sqrt{2}$ is irrational --- it cannot be expressed as a ratio of two integers.

  The proof is by contradiction: we assume $\sqrt{2}$ is rational, meaning
  $\sqrt{2} = a/b$ for some integers $a$ and $b$ with no common factor.
  Squaring both sides gives $2 b^2 = a^2$, which means $a^2$ is even,
  so $a$ must be even. But then $a^2$ is divisible by 4, forcing $b^2$ to be even,
  hence $b$ is also even --- contradicting our assumption that $a$ and $b$ share no
  common factor.
\<close>

theorem sqrt_2_irrational: "sqrt 2 \<notin> \<rat>"
proof
  assume "sqrt 2 \<in> \<rat>"
  then obtain a b :: int where
    b_pos: "0 < b" and coprime: "coprime a b" and
    eq: "sqrt 2 = of_int a / of_int b"
    by (rule Rats_cases')
  from eq have "(sqrt 2)\<^sup>2 = (of_int a / of_int b)\<^sup>2" by simp
  hence "2 * (of_int b :: real)\<^sup>2 = (of_int a)\<^sup>2"
    using b_pos by (simp add: field_simps)
  hence int_eq: "2 * b\<^sup>2 = a\<^sup>2"
    by (auto simp flip: of_int_mult of_int_power)
  hence "even (a\<^sup>2)" by (metis dvd_triv_left)
  hence a_even: "even a" by simp
  then obtain k :: int where "a = 2 * k" by blast
  with int_eq have "b\<^sup>2 = 2 * k\<^sup>2" by (simp add: power2_eq_square)
  hence "even (b\<^sup>2)" by (metis dvd_triv_left)
  hence "even b" by simp
  with a_even have "\<not> coprime a b"
    by (auto intro: not_coprimeI[of 2])
  with coprime show False by contradiction
qed


section \<open>Consecutive Composite Numbers\<close>

text \<open>
  For any positive integer $N$, there exists a run of $N$ consecutive composite
  (i.e.\ non-prime) numbers.  The classic proof gives an explicit construction:
  the $N$ numbers
  \[
    (N{+}1)! + 2,\quad (N{+}1)! + 3,\quad \ldots,\quad (N{+}1)! + (N{+}1)
  \]
  are all composite, because for each $2 \le k \le N{+}1$ the number $k$ divides
  both $(N{+}1)!$ and $k$ itself, hence $k$ divides $(N{+}1)! + k$.
  Since $(N{+}1)! + k > k > 1$, this is a non-trivial divisor, so the number
  is not prime.
\<close>

text \<open>We first establish a helper lemma: if $k$ divides $n$ and
  $1 < k < n + k$, then $n + k$ is not prime.\<close>

lemma not_prime_of_dvd:
  fixes n k :: nat
  assumes "k dvd n" "1 < k" "0 < n"
  shows "\<not> prime (n + k)"
proof -
  from assms have k_dvd: "k dvd (n + k)" by simp
  have "k \<noteq> 1" using assms by simp
  moreover have "k \<noteq> n + k" using assms by simp
  ultimately show ?thesis
    using k_dvd unfolding prime_nat_iff by blast
qed

text \<open>The main result: for each $k$ with $2 \le k \le N+1$, the number
  $(N+1)! + k$ is composite.\<close>

lemma fact_plus_composite:
  fixes N k :: nat
  assumes "2 \<le> k" "k \<le> N + 1"
  shows "\<not> prime (fact (N + 1) + k)"
proof (rule not_prime_of_dvd)
  show "k dvd fact (N + 1)"
    using dvd_fact[of k "N + 1"] assms by simp
  show "1 < k" using assms by simp
qed auto

text \<open>We can now state the theorem in its standard form: for every $N > 0$,
  there exist $N$ consecutive natural numbers, none of which is prime.\<close>

theorem consecutive_composites:
  fixes N :: nat
  assumes "N > 0"
  shows "\<exists>m. \<forall>i \<in> {1..N}. \<not> prime (m + i)"
proof (intro exI ballI)
  fix i assume "i \<in> {1..N}"
  hence "2 \<le> i + 1" "i + 1 \<le> N + 1" by auto
  hence "\<not> prime (fact (N + 1) + (i + 1))"
    by (rule fact_plus_composite)
  thus "\<not> prime (fact (N + 1) + 1 + i)"
    by (simp add: add.assoc)
qed


section \<open>The AM–GM Inequality\<close>

text \<open>
  The \<^emph>\<open>arithmetic mean – geometric mean\<close> (AM–GM) inequality is one of the
  most fundamental inequalities in mathematics.  For two non-negative real
  numbers $a$ and $b$ it states
  \\[
    \\frac{a + b}{2} \\;\\ge\\; \\sqrt{a \\cdot b}.
  \\]
  Equality holds if and only if $a = b$.

  A slick proof uses the observation that the square of any real number is
  non-negative.  In particular,
  \\[
    (\\sqrt{a} - \\sqrt{b})^2 \\;\\ge\\; 0
    \\;\\;\\Longrightarrow\\;\\;
    a - 2\\sqrt{a b} + b \\;\\ge\\; 0
    \\;\\;\\Longrightarrow\\;\\;
    a + b \\;\\ge\\; 2\\sqrt{a b}.
  \\]
  Dividing by 2 gives the result.
\<close>
theorem am_gm:
  fixes a b :: real
  assumes "a \<ge> 0" "b \<ge> 0"
  shows "(a + b) / 2 \<ge> sqrt (a * b)"
proof -
  text \<open>The key identity: $(\\sqrt{a} - \\sqrt{b})^2 \\ge 0$.\<close>
  have sq_nn: "(sqrt a - sqrt b)^2 \<ge> 0" by simp
  text \<open>Expanding the square gives $a - 2\\sqrt{ab} + b \\ge 0$.\<close>
  have expand: "(sqrt a)^2 - 2 * (sqrt a * sqrt b) + (sqrt b)^2 \<ge> 0"
  proof -
    have "(sqrt a - sqrt b)^2 = (sqrt a)^2 - 2 * (sqrt a * sqrt b) + (sqrt b)^2"
      by (simp add: power2_eq_square algebra_simps)
    with sq_nn show ?thesis by simp
  qed
  have sa: "(sqrt a)^2 = a" using assms by simp
  have sb: "(sqrt b)^2 = b" using assms by simp
  have sab: "sqrt a * sqrt b = sqrt (a * b)"
    using assms by (simp add: real_sqrt_mult)
  from expand sa sb sab
  have ineq: "a + b \<ge> 2 * sqrt (a * b)" by linarith
  show ?thesis using ineq by (simp add: field_simps)
qed


section \<open>Calculus: Integral of Sine\<close>

text \<open>We show $\\int_0^\\pi \\sin x\\, dx = 2$ via the Fundamental Theorem of Calculus,
  using $-\\cos$ as the antiderivative of $\\sin$.\<close>

theorem integral_sin_0_pi:
  "integral {0..pi} sin = 2"
proof (rule integral_unique)
  \<comment> \<open>Apply the FTC with antiderivative @{term "\<lambda>x. - cos x"}.\<close>
  have ftc: "(sin has_integral ((- cos pi) - (- cos 0))) {0..pi}"
  proof (rule fundamental_theorem_of_calculus)
    show "(0::real) \<le> pi" by simp
  next
    fix x :: real
    assume "x \<in> {0..pi}"
    show "((\<lambda>x. - cos x) has_vector_derivative sin x) (at x within {0..pi})"
    proof -
      have "(cos has_field_derivative - sin x) (at x)"
        by (rule DERIV_cos)
      then have "(cos has_vector_derivative - sin x) (at x)"
        by (simp add: has_real_derivative_iff_has_vector_derivative)
      then have "((\<lambda>x. - cos x) has_vector_derivative - (- sin x)) (at x)"
        by (rule has_vector_derivative_minus)
      then have "((\<lambda>x. - cos x) has_vector_derivative sin x) (at x)"
        by simp
      then show ?thesis
        by (rule has_vector_derivative_at_within)
    qed
  qed
  \<comment> \<open>Evaluate: @{term "- cos pi - (- cos 0)"} simplifies to 2.\<close>
  thus "(sin has_integral 2) {0..pi}" by simp
qed

section \<open>The Dottie Number\<close>

text \<open>
  The Dottie number is the unique fixed point of cosine: the value
  @{term "d :: real"} satisfying @{term "cos d = d"}. It is approximately 0.7391
  and has no known closed form. We prove existence via the intermediate value
  theorem, uniqueness via strict monotonicity, and approximate it to three
  decimal places using verified interval arithmetic.
\<close>

lemma cos_1_lt_1: "cos (1::real) < 1"
  by (approximation 10)

text \<open>\\textbf{Existence.} Consider the function $g(x) = \\cos x - x$.
  We have $g(0) = 1 > 0$ and $g(1) = \\cos 1 - 1 < 0$.
  Since $g$ is continuous, the intermediate value theorem gives
  a point $x \\in (0, 1)$ where $g(x) = 0$, i.e.\\ $\\cos x = x$.\<close>

lemma dottie_exists: "\<exists>x::real. 0 < x \<and> x < 1 \<and> cos x = x"
proof -
  define g where "g = (\<lambda>x::real. cos x - x)"
  have g0: "g 0 = 1" unfolding g_def by simp
  have g1: "g 1 < 0" unfolding g_def using cos_1_lt_1 by simp
  have gcont: "continuous_on {0..1} g"
    unfolding g_def by (intro continuous_intros)
  \<comment> \<open>Apply the IVT to @{term g} on @{term "{0..1::real}"} at value 0.\<close>
  from IVT2'[of g 1 0 0] g1 g0 gcont
  have "\<exists>x\<ge>0. x \<le> 1 \<and> g x = 0" by auto
  then obtain x where hx: "0 \<le> x" "x \<le> 1" "g x = 0" by auto
  hence cos_eq: "cos x = x" unfolding g_def by simp
  moreover have "0 < x"
    using hx(1) cos_eq by (cases "x = 0") auto
  moreover have "x < 1"
    using hx(2) cos_eq cos_1_lt_1 by (cases "x = 1") auto
  ultimately show ?thesis by blast
qed

text \<open>\\textbf{Uniqueness.} The function $g(x) = \\cos x - x$ has derivative
  $g'(x) = -\\sin x - 1$, which is strictly negative for $x \\in [0,1]$
  (since $\\sin x \\ge 0$ there).  A function with strictly negative derivative
  is strictly decreasing, so $g$ can have at most one zero.\<close>

lemma dottie_unique:
  fixes x y :: real
  assumes "0 < x" "x < 1" "cos x = x"
    and "0 < y" "y < 1" "cos y = y"
  shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  define g where "g = (\<lambda>x::real. cos x - x)"
  have gx: "g x = 0" unfolding g_def using assms(3) by simp
  have gy: "g y = 0" unfolding g_def using assms(6) by simp
  \<comment> \<open>The derivative of @{term g} is @{term "\<lambda>x. - sin x - 1"}, which is negative on @{term "{0..1}"}.\<close>
  have g_deriv: "\<exists>d. (g has_real_derivative d) (at t) \<and> d < 0"
    if "0 \<le> t" "t \<le> 1" for t
  proof (intro exI conjI)
    show "(g has_real_derivative (- sin t - 1)) (at t)"
      unfolding g_def by (auto intro!: derivative_eq_intros)
    show "- sin t - 1 < 0"
      using sin_ge_zero[of t] that pi_gt3 by linarith
  qed
  \<comment> \<open>By @{thm DERIV_neg_imp_decreasing}, @{term g} is strictly decreasing on @{term "{0..1}"}.\<close>
  have "x < y \<or> y < x" using \<open>x \<noteq> y\<close> by linarith
  thus False
  proof
    assume "x < y"
    from DERIV_neg_imp_decreasing[OF this] g_deriv assms
    have "g y < g x" by auto
    with gx gy show False by simp
  next
    assume "y < x"
    from DERIV_neg_imp_decreasing[OF this] g_deriv assms
    have "g x < g y" by auto
    with gx gy show False by simp
  qed
qed

text \<open>\\textbf{Definition.} Since the fixed point exists and is unique, we can
  define the Dottie number as \<^emph>\<open>the\<close> real number in $(0,1)$ satisfying
  $\\cos d = d$.\<close>

definition dottie :: real where
  "dottie \<equiv> THE x. 0 < x \<and> x < 1 \<and> cos x = x"

lemma dottie_props: "0 < dottie" "dottie < 1" "cos dottie = dottie"
proof -
  obtain x :: real where hx: "0 < x" "x < 1" "cos x = x"
    using dottie_exists by blast
  have unique: "y = x" if "0 < y" "y < 1" "cos y = y" for y :: real
    using dottie_unique[OF hx(1,2,3) that(1,2,3)] by simp
  have the_eq: "(THE x. 0 < x \<and> x < 1 \<and> cos x = x) = x"
  proof (rule the_equality)
    show "0 < x \<and> x < 1 \<and> cos x = x" using hx by blast
  next
    fix y :: real assume "0 < y \<and> y < 1 \<and> cos y = y"
    thus "y = x" using unique by blast
  qed
  hence eq: "dottie = x" unfolding dottie_def by simp
  show "0 < dottie" "dottie < 1" "cos dottie = dottie"
    unfolding eq using hx by auto
qed

text \<open>\\textbf{Approximation.} We pin down the Dottie number to three decimal
  places: $d \\in (0.739,\\, 0.740)$.  The idea is to check that
  $\\cos(0.739) > 0.739$ (so the fixed point is above 0.739) and
  $\\cos(0.740) < 0.740$ (so it is below 0.740).  Isabelle's verified
  interval arithmetic (the @{method approximation} method) handles
  the numerical bounds.\<close>

lemma cos_0739_gt: "cos (739 / 1000 :: real) > 739 / 1000"
  by (approximation 20)

lemma cos_0740_lt: "cos (740 / 1000 :: real) < 740 / 1000"
  by (approximation 20)

lemma dottie_lower: "739 / 1000 < dottie"
proof (rule ccontr)
  assume "\<not> 739 / 1000 < dottie"
  hence le: "dottie \<le> 739 / 1000" by simp
  \<comment> \<open>Since $g$ is strictly decreasing and $g(0.739) > 0$, we have
      $g(d) \\ge g(0.739) > 0$, contradicting $g(d) = 0$.\<close>
  define g where "g = (\<lambda>x::real. cos x - x)"
  have gd: "g dottie = 0" unfolding g_def using dottie_props(3) by simp
  have g739: "g (739/1000) > 0" unfolding g_def using cos_0739_gt by simp
  show False
  proof (cases "dottie = 739 / 1000")
    case True
    with gd g739 show False by simp
  next
    case False
    with le have "dottie < 739 / 1000" by simp
    have "\<exists>d. (g has_real_derivative d) (at t) \<and> d < 0"
      if "0 \<le> t" "t \<le> 1" for t
    proof (intro exI conjI)
      show "(g has_real_derivative (- sin t - 1)) (at t)"
        unfolding g_def by (auto intro!: derivative_eq_intros)
      show "- sin t - 1 < 0"
        using sin_ge_zero[of t] that pi_gt3 by linarith
    qed
    from DERIV_neg_imp_decreasing[OF \<open>dottie < 739/1000\<close>] this dottie_props
    have "g (739/1000) < g dottie" by auto
    with gd g739 show False by simp
  qed
qed

lemma dottie_upper: "dottie < 740 / 1000"
proof (rule ccontr)
  assume "\<not> dottie < 740 / 1000"
  hence le: "740 / 1000 \<le> dottie" by simp
  define g where "g = (\<lambda>x::real. cos x - x)"
  have gd: "g dottie = 0" unfolding g_def using dottie_props(3) by simp
  have g740: "g (740/1000) < 0" unfolding g_def using cos_0740_lt by simp
  show False
  proof (cases "dottie = 740 / 1000")
    case True
    with gd g740 show False by simp
  next
    case False
    with le have "740 / 1000 < dottie" by simp
    have "\<exists>d. (g has_real_derivative d) (at t) \<and> d < 0"
      if "0 \<le> t" "t \<le> 1" for t
    proof (intro exI conjI)
      show "(g has_real_derivative (- sin t - 1)) (at t)"
        unfolding g_def by (auto intro!: derivative_eq_intros)
      show "- sin t - 1 < 0"
        using sin_ge_zero[of t] that pi_gt3 by linarith
    qed
    from DERIV_neg_imp_decreasing[OF \<open>740/1000 < dottie\<close>] this dottie_props
    have "g dottie < g (740/1000)" by auto
    with gd g740 show False by simp
  qed
qed

text \<open>\\textbf{Summary.} Putting it all together: the Dottie number is the unique
  real fixed point of cosine in $(0,1)$, and it lies between 0.739 and 0.740.\<close>

theorem dottie_number:
  "cos dottie = dottie"
  "739 / 1000 < dottie"
  "dottie < 740 / 1000"
  using dottie_props dottie_lower dottie_upper by auto

section \<open>The Gaussian Integral\<close>

text \<open>
  The Gaussian integral is one of the most celebrated results in analysis:
  \[
    \int_{-\infty}^{\infty} e^{-x^2}\, dx = \sqrt{\pi}.
  \]
  Despite having no elementary antiderivative, the function $e^{-x^2}$ integrates
  over the entire real line to give a beautiful closed form involving $\sqrt{\pi}$.
  This result, often attributed to Gauss, underpins the normalisation of the
  Gaussian (normal) probability distribution.

  The connection to the Gamma function is through the identity
  $\Gamma(s) = \int_0^\infty t^{s-1} e^{-t}\, dt$.  Setting $s = 1/2$ and
  substituting $t = x^2$, $dt = 2x\,dx$ gives:
  \begin{align*}
    \Gamma(1/2) &= \int_0^\infty t^{-1/2} e^{-t}\, dt \\
                &= \int_0^\infty (x^2)^{-1/2} e^{-x^2} \cdot 2x\, dx
                 = 2\int_0^\infty e^{-x^2}\, dx.
  \end{align*}
  Hence $\int_0^\infty e^{-x^2}\,dx = \Gamma(1/2)/2 = \sqrt\pi/2$, and by
  symmetry $\int_{-\infty}^\infty e^{-x^2}\,dx = \sqrt\pi$.
\<close>

text \<open>In Isabelle's library, this is encoded as @{thm Gamma_one_half_real}.\<close>

theorem gaussian_integral: "Gamma (1/2 :: real) = sqrt pi"
  by (rule Gamma_one_half_real)

text \<open>We can also express this as an explicit integral using the nn-integral
  representation of the Gamma function.  Instantiating the general formula
  @{thm [source] Gamma_conv_nn_integral_real} at $s = 1/2$ gives:\<close>

corollary gaussian_integral_nn:
  "(\<integral>\<^sup>+ t. ennreal (indicat_real {0..} t * t powr (- (1/2)) / exp t) \<partial>lborel)
    = ennreal (sqrt pi)"
proof -
  have "ennreal (Gamma (1/2 :: real)) =
    (\<integral>\<^sup>+ t. ennreal (indicat_real {0..} t * t powr (1/2 - 1) / exp t) \<partial>lborel)"
    by (rule Gamma_conv_nn_integral_real) simp
  thus ?thesis
    by (simp add: Gamma_one_half_real)
qed


end



