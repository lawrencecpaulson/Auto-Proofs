theory Roth_Index_Count
  imports Roth_Hasse_Support
begin

section \<open>Counting low-weight exponents\<close>

definition roth_box_of ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat)" where
  "roth_box_of m f =
    Abs_poly_mapping (\<lambda>v. if v < m then f v else 0)"

lemma roth_box_of_lookup:
  "Poly_Mapping.lookup (roth_box_of m f) v =
    (if v < m then f v else 0)"
proof -
  have fin: "finite {v. (if v < m then f v else 0) \<noteq> 0}"
    by (rule finite_subset[of _ "{..<m}"]) auto
  show ?thesis unfolding roth_box_of_def using fin by simp
qed

lemma roth_box_of_inj:
  "inj_on (roth_box_of m) (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
proof (rule inj_onI)
  fix f g
  assume f: "f \<in> (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
    and g: "g \<in> (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
    and e: "roth_box_of m f = roth_box_of m g"
  show "f = g"
  proof (rule ext)
    fix v
    show "f v = g v"
    proof (cases "v < m")
      case True
      then show ?thesis using e
        by (metis roth_box_of_lookup)
    next
      case False
      then show ?thesis using f g
        by (auto simp: PiE_def extensional_def)
    qed
  qed
qed

lemma roth_exponent_box_image:
  "roth_exponent_box m r =
    roth_box_of m ` (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
  by (simp add: roth_exponent_box_def roth_box_of_def)

lemma roth_exponent_box_card:
  "card (roth_exponent_box m r) = (\<Prod>v<m. Suc (r v))"
  unfolding roth_exponent_box_image
  by (simp add: card_image roth_box_of_inj card_PiE)

lemma roth_exponent_box_card_pos:
  "0 < card (roth_exponent_box m r)"
  by (simp add: roth_exponent_box_card)

definition roth_center ::
  "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "roth_center r v k = real k / real (r v) - 1/2"

lemma roth_center_sum_zero:
  assumes pos: "0 < r v"
  shows "(\<Sum>k\<le>r v. roth_center r v k) = 0"
proof -
  have gauss: "2 * (\<Sum>k\<le>r v. real k) =
    real (r v) * (real (r v) + 1)"
    by (simp add: atMost_atLeast0 double_gauss_sum)
  have eq: "(\<Sum>k\<le>r v. real k) / real (r v) =
    real (Suc (r v)) / 2"
    using gauss pos by (simp add: field_simps)
  show ?thesis
    by (simp add: roth_center_def sum_subtractf
      sum_divide_distrib[symmetric] eq)
qed

lemma roth_center_square_bound:
  assumes pos: "0 < r v" and k: "k \<le> r v"
  shows "(roth_center r v k)\<^sup>2 \<le> 1/4"
proof -
  have le: "real k / real (r v) \<le> 1"
    using pos k by (simp add: divide_le_eq)
  have nonneg: "0 \<le> real k / real (r v)"
    using pos by simp
  have bounds: "-1/2 \<le> roth_center r v k"
    "roth_center r v k \<le> 1/2"
    using le nonneg unfolding roth_center_def by linarith+
  have "(1/2 - roth_center r v k) *
      (1/2 + roth_center r v k) \<ge> 0"
    using bounds by (intro mult_nonneg_nonneg) auto
  then show ?thesis
    by (simp add: power2_eq_square algebra_simps)
qed

lemma roth_grid_sum_prod:
  fixes g :: "nat \<Rightarrow> nat \<Rightarrow> real"
  assumes "finite S"
  shows "(\<Sum>f\<in>(\<Pi>\<^sub>E v \<in> S. {..r v}).
      (\<Prod>v\<in>S. g v (f v))) =
    (\<Prod>v\<in>S. \<Sum>k\<le>r v. g v k)"
  using prod_sum_PiE[of S "\<lambda>v. {..r v}" g] assms
  by simp

lemma roth_grid_center_sum_zero:
  assumes fin: "finite S" and v: "v \<in> S" and pos: "0 < r v"
  shows "(\<Sum>f\<in>(\<Pi>\<^sub>E w \<in> S. {..r w}).
    roth_center r v (f v)) = 0"
proof -
  let ?g = "\<lambda>w k. if w = v then roth_center r v k else 1"
  have term_eq: "(\<Prod>w\<in>S. ?g w (f w)) =
    roth_center r v (f v)" for f
    using fin v by simp
  have e: "(\<Sum>f\<in>(\<Pi>\<^sub>E w \<in> S. {..r w}).
      roth_center r v (f v)) =
    (\<Prod>w\<in>S. \<Sum>k\<le>r w. ?g w k)"
    using roth_grid_sum_prod[OF fin, of ?g r]
    by (simp only: term_eq)
  have "(\<Prod>w\<in>S. \<Sum>k\<le>r w. ?g w k) = 0"
  proof -
    have zero: "(\<Sum>k\<le>r v. roth_center r v k) = 0"
      by (rule roth_center_sum_zero[of r v, OF pos])
    show ?thesis
    proof (rule prod_zero[OF fin], rule bexI[where x=v])
      show "(\<Sum>k\<le>r v. ?g v k) = 0"
        using zero by simp
      show "v \<in> S" by (rule v)
    qed
  qed
  then show ?thesis using e by simp
qed

lemma roth_grid_center_cross_zero:
  assumes fin: "finite S" and v: "v \<in> S" and w: "w \<in> S"
    and distinct: "v \<noteq> w" and pos: "0 < r v"
  shows "(\<Sum>f\<in>(\<Pi>\<^sub>E u \<in> S. {..r u}).
    roth_center r v (f v) * roth_center r w (f w)) = 0"
proof -
  let ?g = "\<lambda>u k.
    (if u = v then roth_center r v k else 1) *
    (if u = w then roth_center r w k else 1)"
  have term_eq: "(\<Prod>u\<in>S. ?g u (f u)) =
    roth_center r v (f v) * roth_center r w (f w)" for f
    using fin v w by (simp add: prod.distrib)
  have e: "(\<Sum>f\<in>(\<Pi>\<^sub>E u \<in> S. {..r u}).
      roth_center r v (f v) * roth_center r w (f w)) =
    (\<Prod>u\<in>S. \<Sum>k\<le>r u. ?g u k)"
    using roth_grid_sum_prod[OF fin, of ?g r]
    by (simp only: term_eq)
  have "(\<Prod>u\<in>S. \<Sum>k\<le>r u. ?g u k) = 0"
  proof -
    have zero: "(\<Sum>k\<le>r v. roth_center r v k) = 0"
      by (rule roth_center_sum_zero[of r v, OF pos])
    show ?thesis
    proof (rule prod_zero[OF fin], rule bexI[where x=v])
      show "(\<Sum>k\<le>r v. ?g v k) = 0"
        using zero distinct by simp
      show "v \<in> S" by (rule v)
    qed
  qed
  then show ?thesis using e by simp
qed

lemma roth_grid_second_moment:
  assumes fin: "finite S"
    and pos: "\<And>v. v \<in> S \<Longrightarrow> 0 < r v"
  shows "(\<Sum>f\<in>(\<Pi>\<^sub>E v \<in> S. {..r v}).
      (\<Sum>v\<in>S. roth_center r v (f v))\<^sup>2) \<le>
    real (card (\<Pi>\<^sub>E v \<in> S. {..r v})) * real (card S) / 4"
proof -
  let ?F = "(\<Pi>\<^sub>E v \<in> S. {..r v})"
  have finF: "finite ?F"
    by (rule finite_PiE[OF fin]) simp
  have expand_point: "(\<Sum>v\<in>S. roth_center r v (f v))\<^sup>2 =
    (\<Sum>v\<in>S. \<Sum>w\<in>S.
      roth_center r v (f v) * roth_center r w (f w))" for f
  proof -
    have "(\<Sum>v\<in>S. roth_center r v (f v))\<^sup>2 =
      (\<Sum>w\<in>S. \<Sum>v\<in>S.
        roth_center r v (f v) * roth_center r w (f w))"
      by (simp add: power2_eq_square
        sum_distrib_left sum_distrib_right)
    also have "\<dots> = (\<Sum>v\<in>S. \<Sum>w\<in>S.
        roth_center r v (f v) * roth_center r w (f w))"
      by (rule sum.swap)
    finally show ?thesis .
  qed
  have expand: "(\<Sum>f\<in>?F.
      (\<Sum>v\<in>S. roth_center r v (f v))\<^sup>2) =
    (\<Sum>v\<in>S. \<Sum>w\<in>S. \<Sum>f\<in>?F.
      roth_center r v (f v) * roth_center r w (f w))"
  proof -
    have "(\<Sum>f\<in>?F.
        (\<Sum>v\<in>S. roth_center r v (f v))\<^sup>2) =
      (\<Sum>f\<in>?F. \<Sum>v\<in>S. \<Sum>w\<in>S.
        roth_center r v (f v) * roth_center r w (f w))"
      by (simp only: expand_point)
    also have "\<dots> = (\<Sum>v\<in>S. \<Sum>f\<in>?F. \<Sum>w\<in>S.
        roth_center r v (f v) * roth_center r w (f w))"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>v\<in>S. \<Sum>w\<in>S. \<Sum>f\<in>?F.
        roth_center r v (f v) * roth_center r w (f w))"
      by (intro sum.cong refl, rule sum.swap)
    finally show ?thesis .
  qed
  have off: "(\<Sum>f\<in>?F.
      roth_center r v (f v) * roth_center r w (f w)) = 0"
    if v: "v \<in> S" and w: "w \<in> S" and vw: "v \<noteq> w"
    for v w
    by (rule roth_grid_center_cross_zero
      [where S=S and v=v and w=w and r=r])
      (use fin v w vw pos[OF v] in auto)
  have inner: "(\<Sum>w\<in>S. \<Sum>f\<in>?F.
      roth_center r v (f v) * roth_center r w (f w)) =
    (\<Sum>f\<in>?F. (roth_center r v (f v))\<^sup>2)"
    if v: "v \<in> S" for v
  proof -
    have rest: "(\<Sum>w\<in>S - {v}. \<Sum>f\<in>?F.
        roth_center r v (f v) * roth_center r w (f w)) = 0"
      by (intro sum.neutral) (use v off in auto)
    have "(\<Sum>w\<in>S. \<Sum>f\<in>?F.
        roth_center r v (f v) * roth_center r w (f w)) =
      (\<Sum>f\<in>?F. roth_center r v (f v) *
        roth_center r v (f v))"
      using fin v rest by (simp add: sum.remove)
    then show ?thesis by (simp add: power2_eq_square)
  qed
  have diag: "(\<Sum>f\<in>?F. (roth_center r v (f v))\<^sup>2)
    \<le> real (card ?F) / 4" if v: "v \<in> S" for v
  proof -
    have square: "(roth_center r v (f v))\<^sup>2 \<le> 1/4"
      if f: "f \<in> ?F" for f
    proof (rule roth_center_square_bound[of r v "f v"])
      show "0 < r v" by (rule pos[OF v])
      show "f v \<le> r v" using f v
        by (auto simp: PiE_def)
    qed
    have "(\<Sum>f\<in>?F. (roth_center r v (f v))\<^sup>2)
      \<le> (\<Sum>f\<in>?F. 1/4)"
      by (intro sum_mono) (use square in auto)
    then show ?thesis using finF by simp
  qed
  have "(\<Sum>f\<in>?F.
      (\<Sum>v\<in>S. roth_center r v (f v))\<^sup>2) =
    (\<Sum>v\<in>S. \<Sum>f\<in>?F.
      (roth_center r v (f v))\<^sup>2)"
    using expand inner by (simp cong: sum.cong)
  also have "\<dots> \<le> (\<Sum>v\<in>S. real (card ?F) / 4)"
    by (intro sum_mono) (use diag in auto)
  also have "\<dots> = real (card ?F) * real (card S) / 4"
    using fin by (simp add: mult.commute)
  finally show ?thesis .
qed

lemma roth_box_centered_weight:
  "roth_weight m r (roth_box_of m f) - real m / 2 =
    (\<Sum>v<m. roth_center r v (f v))"
proof -
  have "(\<Sum>v<m. roth_center r v (f v)) =
    (\<Sum>v<m. real (f v) / real (r v)) -
      (\<Sum>v<m. 1/2)"
    by (simp add: roth_center_def sum_subtractf)
  also have "\<dots> =
    roth_weight m r (roth_box_of m f) - real m / 2"
    by (simp add: roth_weight_def roth_box_of_lookup)
  finally show ?thesis by simp
qed

lemma roth_box_second_moment:
  assumes pos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
  shows "(\<Sum>I\<in>roth_exponent_box m r.
      (roth_weight m r I - real m / 2)\<^sup>2) \<le>
    real (card (roth_exponent_box m r)) * real m / 4"
proof -
  let ?F = "(\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
  have reindex: "(\<Sum>I\<in>roth_exponent_box m r.
      (roth_weight m r I - real m / 2)\<^sup>2) =
    (\<Sum>f\<in>?F.
      (roth_weight m r (roth_box_of m f) - real m / 2)\<^sup>2)"
    by (rule sum.reindex_cong[OF roth_box_of_inj
      roth_exponent_box_image]) simp
  have grid: "(\<Sum>f\<in>?F.
      (\<Sum>v<m. roth_center r v (f v))\<^sup>2) \<le>
    real (card ?F) * real m / 4"
    using roth_grid_second_moment[of "{..<m}" r] pos
    by simp
  have card_eq: "card ?F = card (roth_exponent_box m r)"
    by (simp add: roth_exponent_box_card card_PiE)
  show ?thesis using reindex grid card_eq
    by (simp add: roth_box_centered_weight)
qed

definition roth_low_indices ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> real \<Rightarrow>
    (nat \<Rightarrow>\<^sub>0 nat) set" where
  "roth_low_indices m r eps =
    {I \<in> roth_exponent_box m r.
      roth_weight m r I \<le> real m * (1-eps) / 2}"

lemma finite_roth_low_indices [simp]:
  "finite (roth_low_indices m r eps)"
  unfolding roth_low_indices_def
  by (rule finite_subset[OF _ finite_roth_exponent_box]) auto

lemma roth_low_indices_subset:
  "roth_low_indices m r eps \<subseteq> roth_exponent_box m r"
  by (auto simp: roth_low_indices_def)

lemma roth_low_indices_count:
  assumes mpos: "0 < m"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and epos: "0 < eps"
  shows "real (card (roth_low_indices m r eps)) *
      real m * eps\<^sup>2 \<le>
    real (card (roth_exponent_box m r))"
proof -
  let ?L = "roth_low_indices m r eps"
  let ?B = "roth_exponent_box m r"
  have low_square: "(real m * eps / 2)\<^sup>2 \<le>
    (roth_weight m r I - real m / 2)\<^sup>2"
    if I: "I \<in> ?L" for I
  proof -
    have weight: "roth_weight m r I \<le> real m * (1-eps) / 2"
      using I by (simp add: roth_low_indices_def)
    have diff: "real m * eps / 2 \<le>
      real m / 2 - roth_weight m r I"
      using weight by (simp add: algebra_simps)
    have nonneg: "0 \<le> real m * eps / 2"
      using epos by simp
    have "(real m * eps / 2)\<^sup>2 \<le>
      (real m / 2 - roth_weight m r I)\<^sup>2"
      by (rule power_mono[OF diff nonneg])
    then show ?thesis
      by (simp add: power2_eq_square algebra_simps)
  qed
  have low_sum: "real (card ?L) * (real m * eps / 2)\<^sup>2 \<le>
    (\<Sum>I\<in>?L. (roth_weight m r I - real m / 2)\<^sup>2)"
  proof -
    have "(\<Sum>I\<in>?L. (real m * eps / 2)\<^sup>2) \<le>
      (\<Sum>I\<in>?L. (roth_weight m r I - real m / 2)\<^sup>2)"
      by (intro sum_mono) (use low_square in auto)
    then show ?thesis by simp
  qed
  have box_sum: "(\<Sum>I\<in>?L.
      (roth_weight m r I - real m / 2)\<^sup>2) \<le>
    (\<Sum>I\<in>?B.
      (roth_weight m r I - real m / 2)\<^sup>2)"
    by (rule sum_mono2[OF finite_roth_exponent_box
      roth_low_indices_subset]) simp
  have box_moment: "(\<Sum>I\<in>?B.
      (roth_weight m r I - real m / 2)\<^sup>2) \<le>
    real (card ?B) * real m / 4"
    by (rule roth_box_second_moment[where m=m and r=r, OF rpos])
  have moment: "real (card ?L) * (real m * eps / 2)\<^sup>2 \<le>
    real (card ?B) * real m / 4"
    using low_sum box_sum box_moment by linarith
  have cancelled: "(real (card ?L) * real m * eps\<^sup>2) *
      (real m / 4) \<le>
    real (card ?B) * (real m / 4)"
    using moment by (simp add: power2_eq_square algebra_simps)
  have "0 < real m / 4" using mpos by simp
  then show ?thesis using cancelled
    by (simp add: mult_le_cancel_right_pos)
qed

lemma roth_low_indices_dimension:
  assumes mpos: "0 < m"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and epos: "0 < eps"
    and gap: "2 * real d < real m * eps\<^sup>2"
  shows "2 * d * card (roth_low_indices m r eps) <
    card (roth_exponent_box m r)"
proof (cases "card (roth_low_indices m r eps) = 0")
  case True
  then show ?thesis using roth_exponent_box_card_pos[of m r]
    by simp
next
  case False
  have cpos: "0 < real (card (roth_low_indices m r eps))"
    using False by (simp add: card_gt_0_iff)
  have strict: "(2 * real d) *
      real (card (roth_low_indices m r eps)) <
    (real m * eps\<^sup>2) *
      real (card (roth_low_indices m r eps))"
    by (rule mult_strict_right_mono[OF gap cpos])
  have bound: "(real m * eps\<^sup>2) *
      real (card (roth_low_indices m r eps)) \<le>
    real (card (roth_exponent_box m r))"
    using roth_low_indices_count[OF mpos rpos epos]
    by (simp add: mult_ac)
  have h: "(2 * real d) *
      real (card (roth_low_indices m r eps)) <
    real (card (roth_exponent_box m r))"
    using strict bound by linarith
  have cast: "real (2 * d * card (roth_low_indices m r eps)) <
    real (card (roth_exponent_box m r))"
    using h by (simp add: of_nat_mult mult_ac)
  show ?thesis by (rule of_nat_less_imp_less[OF cast])
qed

lemma roth_taylor_conditions_dimension:
  assumes mpos: "0 < m"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and epos: "0 < eps"
    and gap: "2 * real d < real m * eps\<^sup>2"
  shows "2 * d *
    card {I \<in> roth_exponent_box m r.
      roth_weight m r I < real m * (1-eps) / 2} <
    card (roth_exponent_box m r)"
proof -
  let ?C = "{I \<in> roth_exponent_box m r.
    roth_weight m r I < real m * (1-eps) / 2}"
  have sub: "?C \<subseteq> roth_low_indices m r eps"
    by (auto simp: roth_low_indices_def)
  have cards: "card ?C \<le> card (roth_low_indices m r eps)"
    by (rule card_mono[OF finite_roth_low_indices sub])
  have "2 * d * card ?C \<le>
    2 * d * card (roth_low_indices m r eps)"
    using cards by (simp add: mult_le_mono1)
  also have "\<dots> < card (roth_exponent_box m r)"
    by (rule roth_low_indices_dimension[OF mpos rpos epos gap])
  finally show ?thesis .
qed

end
