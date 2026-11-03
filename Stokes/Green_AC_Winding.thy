theory Green_AC_Winding
  imports Green_AC_Approximation
begin

lemma green_cauchy_separated_away:
  fixes h :: "real \<Rightarrow> complex"
  assumes rpos: "0 < r"
    and sep: "\<And>t. t \<in> {0..1} \<Longrightarrow> r \<le> norm (h t - z)"
  shows "z \<notin> path_image h"
proof
  assume "z \<in> path_image h"
  then obtain t where t: "t \<in> {0..1}" and eq: "z = h t"
    by (auto simp: path_image_def)
  have "r \<le> 0"
    using sep[OF t] by (simp add: eq)
  with rpos show False by simp
qed

lemma green_cauchy_integrand_bound:
  fixes g p v k z :: complex
  assumes g0: "g \<noteq> z" and p0: "p \<noteq> z"
  shows "norm (k / (p - z) - v / (g - z))
    \<le> norm (k - v) / norm (p - z) +
      norm v * norm (g - p) / (norm (p - z) * norm (g - z))"
proof -
  have invdiff: "inverse (p - z) - inverse (g - z) =
      inverse (p - z) * (g - p) * inverse (g - z)"
    using division_ring_inverse_diff[of "p - z" "g - z"] g0 p0
    by (simp add: algebra_simps)
  have eq1: "k / (p - z) - v / (g - z) =
      (k - v) / (p - z) +
      v * (inverse (p - z) - inverse (g - z))"
    by (simp add: divide_inverse algebra_simps)
  have eq2: "v * (inverse (p - z) - inverse (g - z)) =
      v * (g - p) / ((p - z) * (g - z))"
    using invdiff by (simp add: divide_inverse ac_simps)
  have eq: "k / (p - z) - v / (g - z) =
      (k - v) / (p - z) + v * (g - p) / ((p - z) * (g - z))"
    using eq1 eq2 by simp
  have "norm (k / (p - z) - v / (g - z)) \<le>
      norm ((k - v) / (p - z)) +
      norm (v * (g - p) / ((p - z) * (g - z)))"
    unfolding eq by (rule norm_triangle_ineq)
  then show ?thesis
    by (simp add: norm_divide norm_mult)
qed

lemma green_cauchy_integrand_uniform_bound:
  fixes g p v k z :: complex
    and r d :: real
  assumes rpos: "0 < r"
    and gsep: "r \<le> norm (g - z)"
    and psep: "r / 2 \<le> norm (p - z)"
    and close: "norm (p - g) \<le> d"
    and dnonneg: "0 \<le> d"
  shows "norm (k / (p - z) - v / (g - z))
    \<le> (2 / r) * norm (k - v) +
      (2 * d / r\<^sup>2) * norm v"
proof -
  let ?P = "norm (p - z)"
  let ?G = "norm (g - z)"
  have Ppos: "0 < ?P" and Gpos: "0 < ?G"
    using psep gsep rpos by linarith+
  have invP: "1 / ?P \<le> 2 / r"
    using psep Ppos rpos
    by (simp add: frac_le_eq divide_nonpos_pos; linarith)
  have prod: "(r / 2) * r \<le> ?P * ?G"
    by (rule mult_mono[OF psep gsep])
      (use Ppos Gpos rpos in auto)
  have invPG: "1 / (?P * ?G) \<le> 2 / r\<^sup>2"
    using prod Ppos Gpos rpos
    by (simp add: frac_le_eq divide_nonpos_pos power2_eq_square;
      linarith)
  have b1: "norm (k - v) / ?P \<le> (2 / r) * norm (k - v)"
    using mult_right_mono[OF invP norm_ge_zero[of "k - v"]]
    by (simp add: divide_inverse mult.commute)
  have b2a: "norm v * norm (g - p) \<le> norm v * d"
    using close by (simp add: norm_minus_commute mult_left_mono)
  have b2: "norm v * norm (g - p) / (?P * ?G) \<le>
      (2 * d / r\<^sup>2) * norm v"
    using mult_mono[OF b2a invPG] dnonneg
    by (simp add: divide_inverse algebra_simps)
  have "norm (k / (p - z) - v / (g - z)) \<le>
      norm (k - v) / ?P +
      norm v * norm (g - p) / (?P * ?G)"
    by (rule green_cauchy_integrand_bound)
      (use Ppos Gpos in auto)
  then show ?thesis
    using b1 b2 by linarith
qed

context green_ac_velocity
begin

lemma cauchy_kernel_integral_error:
  fixes p :: "real \<Rightarrow> complex"
    and k :: "real \<Rightarrow> complex"
    and z :: complex
    and r d :: real
  assumes kc: "continuous_on UNIV k"
    and pdef: "p = (\<lambda>t. g 0 + integral {0..t} k)"
    and rpos: "0 < r"
    and gsep: "\<And>t. t \<in> {0..1} \<Longrightarrow> r \<le> norm (g t - z)"
    and psep: "\<And>t. t \<in> {0..1} \<Longrightarrow> r / 2 \<le> norm (p t - z)"
    and close: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (p t - g t) \<le> d"
    and velerr: "integral {0..1} (\<lambda>t. norm (velocity t - k t)) \<le> d"
    and dnonneg: "0 \<le> d"
  shows "norm (contour_integral p (\<lambda>w. 1 / (w - z)) -
      contour_integral g (\<lambda>w. 1 / (w - z))) \<le>
    (2 / r) * d +
      (2 * d / r\<^sup>2) * integral {0..1} (\<lambda>t. norm (velocity t))"
proof -
  let ?I = "{0..1::real}"
  let ?P = "\<lambda>t. k t / (p t - z)"
  let ?G = "\<lambda>t. velocity t / (g t - z)"
  have awayg: "z \<notin> path_image g"
    by (rule green_cauchy_separated_away[OF rpos gsep])
  have awayp: "z \<notin> path_image p"
    by (rule green_cauchy_separated_away[of "r / 2" p z])
      (use rpos psep in auto)
  have pvalid: "valid_path p"
    unfolding pdef by (rule green_continuous_velocity_valid_path[OF kc])
  have pci: "(\<lambda>w. 1 / (w - z)) contour_integrable_on p"
    by (rule contour_integrable_inversediff[OF pvalid awayp])
  have gci: "(\<lambda>w. 1 / (w - z)) contour_integrable_on g"
    by (rule winding_kernel_integrable)
      (use awayg in auto)
  have pder: "vector_derivative p (at t) = k t"
    if "t \<in> ?I - {0,1}" for t
    unfolding pdef
    by (rule green_continuous_velocity_derivative[OF kc])
      (use that in auto)
  have gder: "vector_derivative g (at t) = velocity t"
    if "t \<in> ?I - exceptional" for t
    by (rule vector_derivative_at[OF deriv[OF that]])
  have pint: "?P integrable_on ?I"
  proof (rule integrable_spike[where S="{0,1}"])
    show "(\<lambda>t. (1 / (p t - z)) * vector_derivative p (at t))
        integrable_on ?I"
      using pci by (simp add: contour_integrable_on)
    show "negligible {0,1::real}" by simp
    show "?P t = (1 / (p t - z)) * vector_derivative p (at t)"
      if "t \<in> ?I - {0,1}" for t
      using pder[OF that] by (simp add: divide_inverse mult.commute)
  qed
  have gint: "?G integrable_on ?I"
  proof (rule integrable_spike[where S=exceptional])
    show "(\<lambda>t. (1 / (g t - z)) * vector_derivative g (at t))
        integrable_on ?I"
      using gci by (simp add: contour_integrable_on)
    show "negligible exceptional" by (rule null)
    show "?G t = (1 / (g t - z)) * vector_derivative g (at t)"
      if "t \<in> ?I - exceptional" for t
      using gder[OF that] by (simp add: divide_inverse mult.commute)
  qed
  have vabs: "velocity absolutely_integrable_on ?I"
    by (rule velocity_absolutely_integrable)
  have kabs: "k absolutely_integrable_on ?I"
    using kc by (metis absolutely_integrable_continuous
      continuous_on_subset interval_cbox subset_UNIV)
  have diffabs: "(\<lambda>t. k t - velocity t) absolutely_integrable_on ?I"
    by (rule set_integral_diff(1)[OF kabs vabs])
  have nint: "(\<lambda>t. norm (k t - velocity t)) integrable_on ?I"
    using diffabs by (simp add: absolutely_integrable_on_def)
  have vint: "(\<lambda>t. norm (velocity t)) integrable_on ?I"
    using vabs by (simp add: absolutely_integrable_on_def)
  have w1int: "(\<lambda>t. (2 / r) * norm (k t - velocity t))
      integrable_on ?I"
    using integrable_cmul[OF nint, of "2 / r"]
    by (simp add: scaleR_conv_of_real)
  have w2int: "(\<lambda>t. (2 * d / r\<^sup>2) * norm (velocity t))
      integrable_on ?I"
    using integrable_cmul[OF vint, of "2 * d / r\<^sup>2"]
    by (simp add: scaleR_conv_of_real)
  have wint: "(\<lambda>t. (2 / r) * norm (k t - velocity t) +
      (2 * d / r\<^sup>2) * norm (velocity t)) integrable_on ?I"
    by (rule integrable_add[OF w1int w2int])
  have g_eq0: "contour_integral g (\<lambda>w. 1 / (w - z)) =
      integral ?I (\<lambda>t. (1 / (g t - z)) * velocity t)"
    by (rule contour_integral)
      (use awayg in \<open>auto intro: continuous_on_inversediff\<close>)
  have g_eq: "contour_integral g (\<lambda>w. 1 / (w - z)) =
      integral ?I ?G"
    using g_eq0 by (simp add: divide_inverse mult.commute)
  have p_eq: "contour_integral p (\<lambda>w. 1 / (w - z)) =
      integral ?I ?P"
    unfolding pdef
    by (simp add: green_continuous_velocity_contour_integral[OF kc]
      divide_inverse mult.commute)
  have bound: "norm (integral ?I (\<lambda>t. ?P t - ?G t)) \<le>
      integral ?I (\<lambda>t. (2 / r) * norm (k t - velocity t) +
        (2 * d / r\<^sup>2) * norm (velocity t))"
  proof (rule integral_norm_bound_integral[OF integrable_diff[OF pint gint] wint])
    fix t assume t: "t \<in> ?I"
    show "norm (?P t - ?G t) \<le>
        (2 / r) * norm (k t - velocity t) +
        (2 * d / r\<^sup>2) * norm (velocity t)"
      by (rule green_cauchy_integrand_uniform_bound[OF rpos gsep[OF t]
        psep[OF t] close[OF t] dnonneg])
  qed
  have wint_eq: "integral ?I (\<lambda>t. (2 / r) *
      norm (k t - velocity t) +
      (2 * d / r\<^sup>2) * norm (velocity t)) =
      (2 / r) * integral ?I (\<lambda>t. norm (k t - velocity t)) +
      (2 * d / r\<^sup>2) * integral ?I (\<lambda>t. norm (velocity t))"
    using integral_add[OF w1int w2int] by simp
  have velerr': "integral ?I (\<lambda>t. norm (k t - velocity t)) \<le> d"
    using velerr by (simp add: norm_minus_commute)
  have times_err: "(2 / r) *
      integral ?I (\<lambda>t. norm (k t - velocity t)) \<le> (2 / r) * d"
    by (rule mult_left_mono[OF velerr'])
      (use rpos in auto)
  show ?thesis
    using bound wint_eq times_err
    by (simp add: p_eq g_eq integral_diff[OF pint gint]; linarith)
qed

theorem cauchy_kernel_contour_integral:
  assumes away: "z \<notin> path_image g"
  shows "contour_integral g (\<lambda>w. 1 / (w - z)) =
    2 * pi * \<i> * winding_number g z"
proof -
  have gpath: "path g"
    by (rule green_ac_path_is_path[OF ac])
  have closed: "closed (path_image g)"
    by (rule compact_imp_closed) (rule compact_path_image[OF gpath])
  have nonempty: "path_image g \<noteq> {}"
    by (auto simp: path_image_def)
  define r where "r = infdist z (path_image g)"
  have rpos: "0 < r"
    unfolding r_def
    by (rule infdist_pos_not_in_closed[OF closed nonempty away])
  have gsep: "r \<le> norm (g t - z)" if t: "t \<in> {0..1}" for t
  proof -
    have "r \<le> dist z (g t)"
      unfolding r_def by (rule infdist_le)
        (use t in \<open>auto simp: path_image_def\<close>)
    then show ?thesis
      by (simp add: dist_norm norm_minus_commute)
  qed
  have vabs: "velocity absolutely_integrable_on {0..1}"
    by (rule velocity_absolutely_integrable)
  have vint: "(\<lambda>t. norm (velocity t)) integrable_on {0..1}"
    using vabs by (simp add: absolutely_integrable_on_def)
  define L where "L = integral {0..1} (\<lambda>t. norm (velocity t))"
  have Lnonneg: "0 \<le> L"
    unfolding L_def by (rule integral_nonneg[OF vint]) simp
  let ?W = "2 * pi * \<i> * winding_number g z"
  have approx: "norm (?W -
      contour_integral g (\<lambda>w. 1 / (w - z))) < e"
    if epos: "0 < e" for e :: real
  proof -
    define C where "C = 2 / r + 2 * L / r\<^sup>2"
    have Cpos: "0 < C"
    proof -
      have "0 < 2 / r" using rpos by simp
      moreover have "0 \<le> 2 * L / r\<^sup>2"
        using Lnonneg rpos by simp
      ultimately show ?thesis unfolding C_def by linarith
    qed
    define d where "d = min (r / 4) (e / (2 * C))"
    have dpos: "0 < d"
      using rpos Cpos epos by (simp add: d_def)
    have dsmall: "d \<le> r / 4"
      by (simp add: d_def)
    have dC: "d * C \<le> e / 2"
    proof -
      have "d * C \<le> (e / (2 * C)) * C"
        by (rule mult_right_mono) (use Cpos in \<open>auto simp: d_def\<close>)
      then show ?thesis
        using Cpos by simp
    qed
    obtain k p where kc: "continuous_on UNIV k"
      and pdef: "p = (\<lambda>t. g 0 + integral {0..t} k)"
      and pvalid: "valid_path p"
      and wind: "winding_number p z = winding_number g z"
      and close: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (p t - g t) < d"
      and vel: "integral {0..1} (\<lambda>t. norm (velocity t - k t)) < d"
      using winding_approximants[of z d] away dpos by blast
    have psep: "r / 2 \<le> norm (p t - z)"
      if t: "t \<in> {0..1}" for t
    proof -
      have tri: "norm (g t - z) \<le>
          norm (g t - p t) + norm (p t - z)"
        using norm_triangle_ineq[of "g t - p t" "p t - z"]
        by (simp add: algebra_simps)
      show ?thesis
        using gsep[OF t] close[OF t] tri dsmall rpos
        by (simp add: norm_minus_commute; linarith)
    qed
    have awayp: "z \<notin> path_image p"
      by (rule green_cauchy_separated_away[of "r / 2" p z])
        (use rpos psep in auto)
    have p_eq: "contour_integral p (\<lambda>w. 1 / (w - z)) = ?W"
      using winding_number_valid_path[OF pvalid awayp] wind
      by (simp add: field_simps)
    have error: "norm (contour_integral p (\<lambda>w. 1 / (w - z)) -
        contour_integral g (\<lambda>w. 1 / (w - z))) \<le>
      (2 / r) * d +
        (2 * d / r\<^sup>2) * L"
      using cauchy_kernel_integral_error[OF kc pdef rpos gsep psep]
        close vel dpos
      by (auto simp: L_def less_imp_le)
    have errorC: "(2 / r) * d + (2 * d / r\<^sup>2) * L = d * C"
      unfolding C_def by (simp add: algebra_simps)
    have "norm (?W -
        contour_integral g (\<lambda>w. 1 / (w - z))) \<le> d * C"
      using error p_eq errorC by metis
    then show ?thesis
      using dC epos by linarith
  qed
  show ?thesis
  proof (rule ccontr)
    assume "contour_integral g (\<lambda>w. 1 / (w - z)) \<noteq> ?W"
    then have pos: "0 < norm (?W -
        contour_integral g (\<lambda>w. 1 / (w - z)))"
      by simp
    from approx[OF pos] show False by simp
  qed
qed

corollary winding_number_contour_integral:
  assumes "z \<notin> path_image g"
  shows "winding_number g z =
    1 / (2 * pi * \<i>) *
      contour_integral g (\<lambda>w. 1 / (w - z))"
  using cauchy_kernel_contour_integral[OF assms]
  by (simp add: field_simps)

end

theorem green_ac_winding_number:
  fixes g g' :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and null: "negligible N"
    and deriv: "\<And>t. t \<in> {0..1} - N \<Longrightarrow>
      (g has_vector_derivative g' t) (at t)"
    and away: "z \<notin> path_image g"
  shows "winding_number g z =
    1 / (2 * pi * \<i>) *
      contour_integral g (\<lambda>w. 1 / (w - z))"
proof -
  interpret green_ac_velocity g g' N
    by standard (use ac null deriv in auto)
  show ?thesis
    by (rule winding_number_contour_integral[OF away])
qed

corollary green_ac_winding_number_ac:
  fixes g :: "real \<Rightarrow> complex"
  assumes ac: "absolutely_continuous_on {0..1} g"
    and away: "z \<notin> path_image g"
  shows "winding_number g z =
    1 / (2 * pi * \<i>) *
      contour_integral g (\<lambda>w. 1 / (w - z))"
proof -
  let ?N = "{t \<in> {0..1}. \<not> g differentiable (at t)}"
  have null: "negligible ?N"
    by (rule green_ac_path_derivative_ae[OF ac])
  have deriv: "(g has_vector_derivative (vector_derivative g (at t))) (at t)"
    if "t \<in> {0..1} - ?N" for t
    using that by (simp add: vector_derivative_works)
  show ?thesis
    by (rule green_ac_winding_number[OF ac null deriv away])
qed

lemma green_rectifiable_path_image_negligible:
  fixes g :: "real \<Rightarrow> complex"
  assumes rect: "rectifiable_path g"
  shows "negligible (path_image g)"
proof -
  obtain h where "rectifiable_path h"
    and image: "path_image h = path_image g"
    and "pathstart h = pathstart g"
    and "pathfinish h = pathfinish g"
    and "path_length h = path_length g"
    and "arc g \<Longrightarrow> arc h"
    and "simple_path g \<Longrightarrow> simple_path h"
    and "\<forall>t\<in>{0..1}. path_length (subpath 0 t h) = path_length g * t"
    and lip: "\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}.
        dist (h x) (h y) \<le> path_length g * dist x y"
    by (rule arc_length_reparametrization[OF rect]) blast
  let ?S = "(of_real :: real \<Rightarrow> complex) ` {0..1}"
  have small: "negligible ?S"
    by (rule negligible_differentiable_image_lowdim)
      (auto simp: differentiable_on_def)
  have length_nonneg: "0 \<le> path_length g"
    using path_length_pos_le[OF rect] by simp
  have local_lip:
    "\<exists>T B. open T \<and> x \<in> T \<and>
      (\<forall>y\<in>?S \<inter> T.
        norm (h (Re y) - h (Re x)) \<le> B * norm (y - x))"
    if x: "x \<in> ?S" for x
  proof (intro exI[where x=UNIV] exI[where x="path_length g"] conjI ballI)
    show "open (UNIV :: complex set)" by simp
    show "x \<in> UNIV" by simp
    fix y assume y: "y \<in> ?S \<inter> UNIV"
    have xI: "Re x \<in> {0..1}" and yI: "Re y \<in> {0..1}"
      using x y by auto
    have "norm (h (Re y) - h (Re x)) \<le>
        path_length g * \<bar>Re (y - x)\<bar>"
      using lip xI yI by (simp add: dist_norm)
    also have "\<dots> \<le> path_length g * norm (y - x)"
      by (rule mult_left_mono[OF abs_Re_le_cmod length_nonneg])
    finally show "norm (h (Re y) - h (Re x)) \<le>
        path_length g * norm (y - x)" .
  qed
  have "negligible ((\<lambda>z. h (Re z)) ` ?S)"
    by (rule negligible_locally_Lipschitz_image)
      (use small local_lip in auto)
  then show ?thesis
    using image by (simp add: path_image_def image_comp)
qed

corollary green_ac_path_image_negligible:
  fixes g :: "real \<Rightarrow> complex"
  assumes "absolutely_continuous_on {0..1} g"
  shows "negligible (path_image g)"
  by (rule green_rectifiable_path_image_negligible
    [OF green_ac_path_rectifiable[OF assms]])

end
