theory Green_Cauchy_Area
  imports Green_AC_Measure
begin

definition green_axis_majorant :: "real \<Rightarrow> real \<Rightarrow> real" where
  "green_axis_majorant R x =
    indicator {-R..R} x *\<^sub>R \<bar>x\<bar> powr (-1/2)"

lemma green_half_power_integrable:
  fixes R :: real
  assumes "0 \<le> R"
  shows "set_integrable lborel {0..R} (\<lambda>x. x powr (-1/2))"
proof -
  have "(\<lambda>x. x powr (-1/2)) integrable_on {0..R}"
    by (rule integrable_on_powr_from_0) (use assms in auto)
  then have ai: "(\<lambda>x. x powr (-1/2)) absolutely_integrable_on {0..R}"
    by (subst absolutely_integrable_on_iff_nonneg) auto
  have meas: "(\<lambda>x. indicator {0..R} x *\<^sub>R x powr (-1/2))
      \<in> borel_measurable lborel"
    by measurable
  show ?thesis
    using ai unfolding set_integrable_def
    by (subst (asm) integrable_completion[OF meas]) assumption
qed

lemma green_abs_half_power_integrable:
  fixes R :: real
  assumes R: "0 \<le> R"
  shows "integrable lborel (green_axis_majorant R)"
proof -
  let ?f = "\<lambda>x::real. indicator {0..R} x *\<^sub>R x powr (-1/2)"
  have pos: "integrable lborel ?f"
    using green_half_power_integrable[OF R]
    by (simp add: set_integrable_def)
  have neg: "integrable lborel (\<lambda>x. ?f (-x))"
    using lborel_integrable_real_affine[OF pos, where c="-1" and t=0]
    by simp
  have eq: "green_axis_majorant R x =
      ?f x + ?f (-x)" for x
    using R by (cases "x < 0")
      (auto simp: green_axis_majorant_def indicator_def)
  have eq_fun: "green_axis_majorant R =
      (\<lambda>x. ?f x + ?f (-x))"
    by (rule ext) (rule eq)
  show ?thesis
    unfolding eq_fun
    by (rule Bochner_Integration.integrable_add[OF pos neg])
qed

lemma green_half_power_product_integrable:
  fixes R :: real
  assumes R: "0 \<le> R"
  shows "integrable (lborel \<Otimes>\<^sub>M lborel)
    (\<lambda>(x,y). green_axis_majorant R x * green_axis_majorant R y)"
proof -
  let ?h = "green_axis_majorant R"
  have hint: "integrable lborel ?h"
    by (rule green_abs_half_power_integrable[OF R])
  have hpos: "0 \<le> ?h x" for x
    by (simp add: green_axis_majorant_def indicator_def)
  have meas: "(\<lambda>(x,y). ?h x * ?h y)
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using borel_measurable_integrable[OF hint] by measurable
  have inner: "integrable lborel (\<lambda>y. ?h x * ?h y)" for x
    by (rule Bochner_Integration.integrable_mult_right) (rule hint)
  have norm_eq: "(\<integral>y. norm (?h x * ?h y) \<partial>lborel) =
      ?h x * (\<integral>y. ?h y \<partial>lborel)" for x
    using hpos[of x] by (simp add: abs_mult hpos)
  have outer: "integrable lborel
      (\<lambda>x. \<integral>y. norm (?h x * ?h y) \<partial>lborel)"
    unfolding norm_eq
    by (rule Bochner_Integration.integrable_mult_left) (rule hint)
  show ?thesis
    by (rule lborel_pair.Fubini_integrable)
      (use meas outer inner in auto)
qed

lemma green_complex_pair_measurable:
  "(\<lambda>(x::real,y::real). Complex x y)
    \<in> (lborel :: (real \<times> real) measure) \<rightarrow>\<^sub>M borel"
proof -
  have "continuous_on UNIV
      (\<lambda>p::real \<times> real. Complex (fst p) (snd p))"
    by (intro continuous_on_Complex continuous_on_fst
      continuous_on_snd continuous_on_id)
  then show ?thesis
    by (simp add: borel_measurable_continuous_onI case_prod_beta)
qed

lemma green_complex_half_power_product_integrable:
  fixes R :: real
  assumes R: "0 \<le> R"
  shows "integrable (lborel :: complex measure)
    (\<lambda>z. green_axis_majorant R (Re z) *
      green_axis_majorant R (Im z))"
proof -
  let ?h = "green_axis_majorant R"
  let ?F = "\<lambda>z::complex. ?h (Re z) * ?h (Im z)"
  let ?C = "\<lambda>(x::real,y::real). Complex x y"
  have measC: "?C \<in> (lborel :: (real \<times> real) measure) \<rightarrow>\<^sub>M borel"
    by (rule green_complex_pair_measurable)
  have measF: "?F \<in> borel_measurable (borel :: complex measure)"
    unfolding green_axis_majorant_def by measurable
  have prod: "integrable (lborel :: (real \<times> real) measure) (\<lambda>(x,y). ?h x * ?h y)"
    using green_half_power_product_integrable[OF R]
    by (simp add: lborel_prod)
  have prod': "integrable (lborel :: (real \<times> real) measure)
      (\<lambda>p. ?h (fst p) * ?h (snd p))"
    using prod by (simp add: split_def)
  have eq: "(\<lambda>p. ?F (?C p)) =
      (\<lambda>p. ?h (fst p) * ?h (snd p))"
    by (rule ext) (case_tac p, simp)
  have int: "integrable (lborel :: (real \<times> real) measure)
      (\<lambda>p. ?F (?C p))"
    unfolding eq by (rule prod')
  have "integrable (distr (lborel :: (real \<times> real) measure) borel ?C) ?F"
    using int integrable_distr_eq[OF measC measF] by blast
  then show ?thesis
    by (simp only: lborel_distr_complex_pair)
qed

lemma green_inverse_cmod_bound:
  fixes z :: complex
  assumes re: "Re z \<noteq> 0" and im: "Im z \<noteq> 0"
  shows "1 / norm z \<le>
    \<bar>Re z\<bar> powr (-1/2) * \<bar>Im z\<bar> powr (-1/2)"
proof -
  let ?a = "\<bar>Re z\<bar>"
  let ?b = "\<bar>Im z\<bar>"
  have apos: "0 < ?a" and bpos: "0 < ?b"
    using re im by auto
  have npos: "0 < norm z"
    using re by auto
  have ab_le: "?a * ?b \<le> (norm z)\<^sup>2"
  proof -
    have a_le: "?a \<le> norm z" by (rule abs_Re_le_cmod)
    have b_le: "?b \<le> norm z" by (rule abs_Im_le_cmod)
    have "?a * ?b \<le> norm z * norm z"
      by (rule mult_mono[OF a_le b_le])
        (use apos bpos in auto)
    then show ?thesis
      by (simp add: power2_eq_square)
  qed
  have sqrt_le: "sqrt (?a * ?b) \<le> norm z"
    using real_sqrt_le_mono[OF ab_le] by simp
  have inv_le: "1 / norm z \<le> 1 / sqrt (?a * ?b)"
    using sqrt_le apos bpos npos by (simp add: frac_le)
  have rhs: "?a powr (-1/2) * ?b powr (-1/2) =
      1 / sqrt (?a * ?b)"
    using apos bpos
    by (simp add: powr_mult[symmetric] powr_minus_divide
      powr_half_sqrt real_sqrt_mult)
  show ?thesis
    using inv_le rhs by simp
qed

lemma green_complex_axes_ae:
  "AE z in (lborel :: complex measure).
    Re z \<noteq> 0 \<and> Im z \<noteq> 0"
proof -
  let ?C = "\<lambda>(x::real,y::real). Complex x y"
  have measC: "?C \<in> (lborel :: (real \<times> real) measure) \<rightarrow>\<^sub>M borel"
    by (rule green_complex_pair_measurable)
  have ae_pair: "AE p in (lborel :: (real \<times> real) measure).
      fst p \<noteq> 0 \<and> snd p \<noteq> 0"
  proof -
    have zero: "{0::real} \<in> null_sets lborel"
      using AE_lborel_singleton[of "0::real"]
      by (simp add: AE_iff_null_sets)
    have ax1: "{0::real} \<times> UNIV \<in>
        null_sets (lborel :: (real \<times> real) measure)"
      unfolding lborel_prod[symmetric]
      by (rule lborel.times_in_null_sets1[OF zero]) simp
    have ax2: "UNIV \<times> {0::real} \<in>
        null_sets (lborel :: (real \<times> real) measure)"
      unfolding lborel_prod[symmetric]
      by (rule lborel.times_in_null_sets2) (use zero in auto)
    have ax: "{p::real \<times> real. fst p = 0 \<or> snd p = 0}
        \<in> null_sets lborel"
      using ax1 ax2
      by (subgoal_tac "{p::real \<times> real. fst p = 0 \<or> snd p = 0} =
          ({0} \<times> UNIV) \<union> (UNIV \<times> {0})")
        auto
    show ?thesis
      by (rule AE_I'[OF ax]) auto
  qed
  have Pmeas: "{z \<in> space (borel :: complex measure).
      Re z \<noteq> 0 \<and> Im z \<noteq> 0} \<in> sets borel"
    by measurable
  have aeC: "AE z in distr (lborel :: (real \<times> real) measure) borel ?C.
      Re z \<noteq> 0 \<and> Im z \<noteq> 0"
    using ae_pair
    by (subst AE_distr_iff[OF measC Pmeas])
      (simp add: case_prod_beta)
  have eq: "distr (lborel :: (real \<times> real) measure) borel ?C =
      (lborel :: complex measure)"
    by (rule lborel_distr_complex_pair)
  have aeC': "AE z in (lborel :: complex measure).
      Re z \<noteq> 0 \<and> Im z \<noteq> 0"
    using aeC[unfolded eq] .
  show ?thesis
    by (rule aeC')
qed

lemma green_inverse_cmod_integrable_square:
  fixes R :: real
  assumes R: "0 \<le> R"
  shows "integrable (lborel :: complex measure)
    (\<lambda>z. indicator {z. \<bar>Re z\<bar> \<le> R \<and> \<bar>Im z\<bar> \<le> R} z
      *\<^sub>R (1 / norm z))"
proof -
  let ?S = "{z::complex. \<bar>Re z\<bar> \<le> R \<and> \<bar>Im z\<bar> \<le> R}"
  let ?h = "green_axis_majorant R"
  let ?F = "\<lambda>z::complex. ?h (Re z) * ?h (Im z)"
  let ?K = "\<lambda>z::complex. indicator ?S z *\<^sub>R (1 / norm z)"
  have Fint: "integrable lborel ?F"
    by (rule green_complex_half_power_product_integrable[OF R])
  have Kmeas: "?K \<in> borel_measurable lborel"
    by measurable
  have Fnonneg: "0 \<le> ?F z" for z
    by (simp add: green_axis_majorant_def indicator_def)
  have bound: "AE z in lborel. norm (?K z) \<le> norm (?F z)"
    using green_complex_axes_ae
  proof eventually_elim
    fix z :: complex
    assume nz: "Re z \<noteq> 0 \<and> Im z \<noteq> 0"
    show "norm (?K z) \<le> norm (?F z)"
    proof (cases "z \<in> ?S")
      case True
      have reI: "Re z \<in> {-R..R}" and imI: "Im z \<in> {-R..R}"
        using True by auto
      have eqF: "?F z =
          \<bar>Re z\<bar> powr (-1/2) * \<bar>Im z\<bar> powr (-1/2)"
        using reI imI by (simp add: green_axis_majorant_def indicator_def)
      have eqK: "norm (?K z) = 1 / norm z"
        using True by simp
      have eqNormF: "norm (?F z) =
          \<bar>Re z\<bar> powr (-1/2) * \<bar>Im z\<bar> powr (-1/2)"
        using eqF Fnonneg[of z] by simp
      show ?thesis
        unfolding eqK eqNormF
        by (rule green_inverse_cmod_bound[OF nz[THEN conjunct1]
          nz[THEN conjunct2]])
    next
      case False
      then have eqK: "norm (?K z) = 0"
        by simp
      show ?thesis
        unfolding eqK
        by simp
    qed
  qed
  show ?thesis
    by (rule Bochner_Integration.integrable_bound[OF Fint Kmeas bound])
qed

lemma green_inverse_cmod_integrable_cball:
  fixes R :: real
  assumes R: "0 \<le> R"
  shows "integrable (lborel :: complex measure)
    (\<lambda>z. indicator (cball 0 R) z *\<^sub>R (1 / norm z))"
proof -
  let ?S = "{z::complex. \<bar>Re z\<bar> \<le> R \<and> \<bar>Im z\<bar> \<le> R}"
  let ?B = "cball (0::complex) R"
  let ?F = "\<lambda>z::complex. indicator ?S z *\<^sub>R (1 / norm z)"
  have sub: "?B \<subseteq> ?S"
  proof
    fix z assume z: "z \<in> ?B"
    have "norm z \<le> R"
      using z by simp
    then show "z \<in> ?S"
      using abs_Re_le_cmod[of z] abs_Im_le_cmod[of z] by auto
  qed
  have Fint: "integrable lborel ?F"
    by (rule green_inverse_cmod_integrable_square[OF R])
  have Bmeas: "?B \<in> sets (lborel :: complex measure)"
    by simp
  have int: "integrable lborel
      (\<lambda>z. indicator ?B z *\<^sub>R ?F z)"
    by (rule Bochner_Integration.integrable_mult_indicator[OF Bmeas Fint])
  have eq: "indicator ?B z *\<^sub>R ?F z =
      indicator ?B z *\<^sub>R (1 / norm z)" for z
    using sub by (auto simp: indicator_def)
  show ?thesis
    using int by (simp only: eq)
qed

lemma green_inverse_distance_integrable_cball:
  fixes w :: complex
  assumes R: "0 \<le> R"
  shows "integrable (lborel :: complex measure)
    (\<lambda>z. indicator (cball w R) z *\<^sub>R (1 / norm (z - w)))"
proof -
  let ?H = "\<lambda>z::complex. indicator (cball 0 R) z *\<^sub>R (1 / norm z)"
  have Hint: "integrable (lborel :: complex measure) ?H"
    by (rule green_inverse_cmod_integrable_cball[OF R])
  have Tmeas: "((+) (-w)) \<in> (lborel :: complex measure) \<rightarrow>\<^sub>M borel"
    by measurable
  have int: "integrable lborel (\<lambda>z. ?H (-w + z))"
    by (rule integrable_distr[OF Tmeas])
      (use Hint in \<open>simp add: lborel_distr_plus\<close>)
  have eq: "?H (-w + z) =
      indicator (cball w R) z *\<^sub>R (1 / norm (z - w))" for z
  proof -
    have "((z - w) \<in> cball 0 R) = (z \<in> cball w R)"
      by (simp add: dist_norm)
    then show ?thesis
      by (simp add: algebra_simps indicator_def)
  qed
  show ?thesis
    using int by (simp only: eq)
qed

lemma green_inverse_distance_integral_cball:
  fixes w :: complex
  assumes R: "0 \<le> R"
  shows "(\<integral>z. indicator (cball w R) z *\<^sub>R
      (1 / norm (z - w)) \<partial>(lborel :: complex measure)) =
    (\<integral>z. indicator (cball 0 R) z *\<^sub>R
      (1 / norm z) \<partial>(lborel :: complex measure))"
proof -
  let ?H = "\<lambda>z::complex. indicator (cball 0 R) z *\<^sub>R (1 / norm z)"
  have Tmeas: "((+) (-w)) \<in> (lborel :: complex measure) \<rightarrow>\<^sub>M borel"
    by measurable
  have Bmeas: "cball (0::complex) R \<in> sets borel"
    by simp
  have Hmeas: "?H \<in> borel_measurable (borel :: complex measure)"
    using Bmeas by measurable
  have eq: "?H (-w + z) =
      indicator (cball w R) z *\<^sub>R (1 / norm (z - w))" for z
    by (auto simp: indicator_def dist_norm)
  have "(\<integral>z. ?H z \<partial>(lborel :: complex measure)) =
      (\<integral>z. ?H (-w + z) \<partial>lborel)"
    using integral_distr[OF Tmeas Hmeas]
    by (simp add: lborel_distr_plus)
  then show ?thesis
    by (simp only: eq)
qed

lemma green_cauchy_area_kernel_pointwise_bound:
  fixes u :: "complex \<Rightarrow> complex"
  assumes C: "\<And>z. norm (u z) \<le> C"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and Cnonneg: "0 \<le> C"
    and T: "R + norm w \<le> T"
  shows "norm (u z / (z - w)) \<le>
    C * (indicator (cball w T) z *\<^sub>R (1 / norm (z - w)))"
proof (cases "z \<in> cball w T")
  case True
  then show ?thesis
    using C[of z] Cnonneg
    by (simp add: indicator_def norm_divide divide_right_mono)
next
  case False
  have "z \<notin> cball 0 R"
  proof
    assume z: "z \<in> cball 0 R"
    have "norm (z - w) \<le> norm z + norm w"
      using norm_triangle_ineq[of z "-w"] by (simp add: norm_minus_commute)
    then have "dist z w \<le> T"
      using z T by (simp add: dist_norm; linarith)
    then show False
      using False by (simp add: dist_commute)
  qed
  then show ?thesis
    using supp[of z] False by (simp add: indicator_def)
qed

lemma green_cauchy_area_kernel_integrable:
  fixes u :: "complex \<Rightarrow> complex"
  assumes uc: "continuous_on UNIV u"
    and C: "\<And>z. norm (u z) \<le> C"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and R: "0 \<le> R"
    and Cnonneg: "0 \<le> C"
  shows "integrable (lborel :: complex measure)
    (\<lambda>z. u z / (z - w))"
proof -
  let ?T = "R + norm w"
  let ?B = "cball w ?T"
  let ?H = "\<lambda>z::complex. indicator ?B z *\<^sub>R (1 / norm (z - w))"
  have Tnonneg: "0 \<le> ?T"
    using R by simp
  have Hint: "integrable lborel ?H"
    by (rule green_inverse_distance_integrable_cball[OF Tnonneg])
  have maj: "integrable lborel (\<lambda>z. C * ?H z)"
    by (rule Bochner_Integration.integrable_mult_right) (rule Hint)
  have umeas: "u \<in> borel_measurable (lborel :: complex measure)"
    using uc by (simp add: borel_measurable_continuous_onI)
  have Kmeas: "(\<lambda>z. u z / (z - w)) \<in>
      borel_measurable (lborel :: complex measure)"
    using umeas by measurable
  have bound: "norm (u z / (z - w)) \<le> norm (C * ?H z)" for z
  proof -
    have "norm (u z / (z - w)) \<le> C * ?H z"
      by (rule green_cauchy_area_kernel_pointwise_bound
        [OF C supp Cnonneg order_refl])
    then show ?thesis
      using Cnonneg by (simp add: indicator_def)
  qed
  show ?thesis
    by (rule Bochner_Integration.integrable_bound[OF maj Kmeas])
      (rule AE_I2[OF bound])
qed

lemma green_cauchy_area_kernel_integral_bound:
  fixes u :: "complex \<Rightarrow> complex"
  assumes uc: "continuous_on UNIV u"
    and C: "\<And>z. norm (u z) \<le> C"
    and supp: "\<And>z. z \<notin> cball 0 R \<Longrightarrow> u z = 0"
    and R: "0 \<le> R"
    and Cnonneg: "0 \<le> C"
    and B: "norm w \<le> B"
  shows "(\<integral>z. norm (u z / (z - w)) \<partial>(lborel :: complex measure)) \<le>
    C * (\<integral>z. indicator (cball 0 (R + B)) z *\<^sub>R
      (1 / norm z) \<partial>(lborel :: complex measure))"
proof -
  let ?T = "R + B"
  let ?H = "\<lambda>z::complex. indicator (cball w ?T) z *\<^sub>R
    (1 / norm (z - w))"
  have Tnonneg: "0 \<le> ?T"
    using R B norm_ge_zero[of w] by linarith
  have Hint: "integrable lborel ?H"
    by (rule green_inverse_distance_integrable_cball[OF Tnonneg])
  have CHint: "integrable lborel (\<lambda>z. C * ?H z)"
    by (rule Bochner_Integration.integrable_mult_right[OF Hint])
  have Kint: "integrable (lborel :: complex measure)
      (\<lambda>z. u z / (z - w))"
    by (rule green_cauchy_area_kernel_integrable[OF uc C supp R Cnonneg])
  have bound: "norm (u z / (z - w)) \<le> C * ?H z" for z
    by (rule green_cauchy_area_kernel_pointwise_bound[OF C supp Cnonneg])
      (use B in auto)
  have "(\<integral>z. norm (u z / (z - w)) \<partial>(lborel :: complex measure)) \<le>
      (\<integral>z. C * ?H z \<partial>lborel)"
    by (rule Bochner_Integration.integral_mono[OF _ _ bound])
      (use Kint CHint in auto)
  also have "\<dots> = C * (\<integral>z. indicator (cball 0 ?T) z *\<^sub>R
      (1 / norm z) \<partial>(lborel :: complex measure))"
    by (simp only: Bochner_Integration.integral_mult_right_zero
      green_inverse_distance_integral_cball[OF Tnonneg])
  finally show ?thesis .
qed

end
