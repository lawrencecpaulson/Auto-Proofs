theory Green_Rectangle_Contour
  imports Stokes_Local "HOL-Complex_Analysis.Contour_Integration"
begin

text \<open>The real part of this complex differential is \<open>P dx + Q dy\<close>.\<close>
definition green_contour_coefficient ::
    "(real \<times> real \<Rightarrow> real) \<Rightarrow> (real \<times> real \<Rightarrow> real) \<Rightarrow> complex \<Rightarrow> complex" where
  "green_contour_coefficient P Q z = Complex (P (Re z, Im z)) (- Q (Re z, Im z))"

lemma integral_lborel_Icc:
  fixes f :: "real \<Rightarrow> real"
  assumes "set_integrable lborel {a..b} f"
  shows "integral {a..b} f = (LINT x:{a..b}|lborel. f x)"
proof -
  have indicator: "(\<lambda>x. indicator {a..b} x *\<^sub>R f x) =
      (\<lambda>x. if x \<in> {a..b} then f x else 0)"
    by (rule ext) (auto simp: indicator_def of_bool_def split: if_splits)
  have "((\<lambda>x. indicator {a..b} x *\<^sub>R f x) has_integral
      (LINT x:{a..b}|lborel. f x)) UNIV"
    using assms unfolding set_integrable_def set_lebesgue_integral_def
    by (rule has_integral_integral_lborel)
  then have "((\<lambda>x. if x \<in> {a..b} then f x else 0) has_integral
      (LINT x:{a..b}|lborel. f x)) UNIV"
    by (simp only: indicator)
  then have "(f has_integral (LINT x:{a..b}|lborel. f x)) {a..b}"
    using has_integral_restrict_UNIV by blast
  then show ?thesis by (rule integral_unique)
qed

lemma lborel_integral_singleton_zero:
  fixes f :: "real \<Rightarrow> real"
  shows "(LINT x:{a}|lborel. f x) = 0"
  using integral_lborel_Icc[where f=f and a=a and b=a]
  by (simp add: borel_integrable_atLeastAtMost')

lemma Re_integral_complex_Icc:
  fixes f :: "real \<Rightarrow> complex"
  assumes "continuous_on {a..b} f"
  shows "Re (integral {a..b} f) = integral {a..b} (\<lambda>x. Re (f x))"
  using integral_linear[OF integrable_continuous_real[OF assms] bounded_linear_Re]
  by (simp add: comp_def)

lemma Im_integral_complex_Icc:
  fixes f :: "real \<Rightarrow> complex"
  assumes "continuous_on {a..b} f"
  shows "Im (integral {a..b} f) = integral {a..b} (\<lambda>x. Im (f x))"
  using integral_linear[OF integrable_continuous_real[OF assms] bounded_linear_Im]
  by (simp add: comp_def)

lemma contour_integral_horizontal:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "a \<le> b"
  shows "contour_integral (linepath (Complex a c) (Complex b c)) f =
    integral {a..b} (\<lambda>x. f (Complex x c))"
proof (cases "a = b")
  case True
  then show ?thesis by simp
next
  case False
  with assms have ab: "a < b" by simp
  have path: "linepath (Complex a c) (Complex b c) =
      ((+) (Complex 0 c)) \<circ> linepath (of_real a) (of_real b)"
    by (rule ext) (simp add: linepath_def Complex_eq algebra_simps)
  show ?thesis
    unfolding path
    using ab
    by (simp add: contour_integral_translate contour_integral_linepath_Reals_eq
      Complex_eq algebra_simps)
qed

lemma green_contour_continuous:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes ab: "a \<le> b" and cd: "c \<le> d"
    and P: "continuous_on ({a..b} \<times> {c..d}) P"
    and Q: "continuous_on ({a..b} \<times> {c..d}) Q"
  shows "continuous_on (cbox (Complex a c) (Complex b d))
    (green_contour_coefficient P Q)"
proof -
  have coord: "continuous_on (cbox (Complex a c) (Complex b d))
      (\<lambda>z. (Re z, Im z))"
    by (intro continuous_intros)
  have image: "(\<lambda>z. (Re z, Im z)) ` cbox (Complex a c) (Complex b d)
      \<subseteq> {a..b} \<times> {c..d}"
    by (auto simp: in_cbox_complex_iff)
  have PC: "continuous_on (cbox (Complex a c) (Complex b d))
      (\<lambda>z. P (Re z, Im z))"
    by (rule continuous_on_compose2[OF P coord image])
  have QC: "continuous_on (cbox (Complex a c) (Complex b d))
      (\<lambda>z. Q (Re z, Im z))"
    by (rule continuous_on_compose2[OF Q coord image])
  show ?thesis
    unfolding green_contour_coefficient_def
    by (intro continuous_intros PC QC)
qed

lemma green_rectangle_contour_edges:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes ab: "a \<le> b" and cd: "c \<le> d"
    and P: "continuous_on ({a..b} \<times> {c..d}) P"
    and Q: "continuous_on ({a..b} \<times> {c..d}) Q"
  shows "Re (contour_integral (rectpath (Complex a c) (Complex b d))
      (green_contour_coefficient P Q)) =
    (LINT x:{a..b}|lborel. P (x,c)) +
    (LINT y:{c..d}|lborel. Q (b,y)) -
    (LINT x:{a..b}|lborel. P (x,d)) -
    (LINT y:{c..d}|lborel. Q (a,y))"
proof -
  let ?F = "green_contour_coefficient P Q"
  let ?B = "cbox (Complex a c) (Complex b d)"
  let ?p1 = "Complex a c"
  let ?p2 = "Complex b c"
  let ?p3 = "Complex b d"
  let ?p4 = "Complex a d"
  have F_cont: "continuous_on ?B ?F"
    by (rule green_contour_continuous[OF ab cd P Q])
  have edge_cont: "continuous_on (closed_segment u v) ?F"
    if "u \<in> ?B" "v \<in> ?B" for u v
    by (rule continuous_on_subset[OF F_cont])
      (use that in \<open>meson convex_box convex_contains_segment\<close>)
  have corners: "?p1 \<in> ?B" "?p2 \<in> ?B" "?p3 \<in> ?B" "?p4 \<in> ?B"
    using ab cd by (auto simp: in_cbox_complex_iff)
  have cint: "?F contour_integrable_on (linepath u v)"
    if "u \<in> ?B" "v \<in> ?B" for u v
    by (rule contour_integrable_continuous_linepath[OF edge_cont[OF that]])
  have split: "contour_integral (rectpath ?p1 ?p3) ?F =
      contour_integral (linepath ?p1 ?p2) ?F +
      contour_integral (linepath ?p2 ?p3) ?F +
      contour_integral (linepath ?p3 ?p4) ?F +
      contour_integral (linepath ?p4 ?p1) ?F"
    unfolding rectpath_def Let_def
    using corners by (simp add: cint add.assoc)
  have P_horizontal_cont: "continuous_on {a..b} (\<lambda>x. P (x,y))"
    if "y \<in> {c..d}" for y
    by (rule continuous_on_compose2[OF P])
      (use that in \<open>auto intro!: continuous_intros\<close>)
  have Q_vertical_cont: "continuous_on {c..d} (\<lambda>y. Q (x,y))"
    if "x \<in> {a..b}" for x
    by (rule continuous_on_compose2[OF Q])
      (use that in \<open>auto intro!: continuous_intros\<close>)
  have F_horizontal_cont: "continuous_on {a..b} (\<lambda>x. ?F (Complex x y))"
    if "y \<in> {c..d}" for y
    by (rule continuous_on_compose2[OF F_cont])
      (use ab cd that in \<open>auto intro!: continuous_intros simp: in_cbox_complex_iff\<close>)
  have F_vertical_cont: "continuous_on {c..d} (\<lambda>y. ?F (Complex x y))"
    if "x \<in> {a..b}" for x
    by (rule continuous_on_compose2[OF F_cont])
      (use ab cd that in \<open>auto intro!: continuous_intros simp: in_cbox_complex_iff\<close>)
  have bottom: "Re (contour_integral (linepath ?p1 ?p2) ?F) =
      (LINT x:{a..b}|lborel. P (x,c))"
    using P_horizontal_cont[of c] F_horizontal_cont[of c] cd
    by (simp add: contour_integral_horizontal[OF ab] green_contour_coefficient_def
      Re_integral_complex_Icc integral_lborel_Icc[OF borel_integrable_atLeastAtMost'])
  have right: "Re (contour_integral (linepath ?p2 ?p3) ?F) =
      (LINT y:{c..d}|lborel. Q (b,y))"
    using Q_vertical_cont[of b] F_vertical_cont[of b] ab cd
    by (cases "c = d")
      (simp_all add: contour_integral_linepath_same_Re green_contour_coefficient_def
        Im_integral_complex_Icc lborel_integral_singleton_zero
        integral_lborel_Icc[OF borel_integrable_atLeastAtMost'])
  have top: "Re (contour_integral (linepath ?p3 ?p4) ?F) =
      - (LINT x:{a..b}|lborel. P (x,d))"
    using P_horizontal_cont[of d] F_horizontal_cont[of d] cd
      edge_cont[OF corners(3,4)]
    by (simp add: contour_integral_reverse_linepath contour_integral_horizontal[OF ab]
      green_contour_coefficient_def Re_integral_complex_Icc
      integral_lborel_Icc[OF borel_integrable_atLeastAtMost'])
  have left: "Re (contour_integral (linepath ?p4 ?p1) ?F) =
      - (LINT y:{c..d}|lborel. Q (a,y))"
    using Q_vertical_cont[of a] F_vertical_cont[of a] ab cd
      edge_cont[OF corners(4,1)]
    by (cases "c = d")
      (simp_all add: contour_integral_reverse_linepath contour_integral_linepath_same_Re
        green_contour_coefficient_def Im_integral_complex_Icc
        lborel_integral_singleton_zero
        integral_lborel_Icc[OF borel_integrable_atLeastAtMost'])
  show ?thesis using split bottom right top left by simp
qed

theorem Green_rectangle_contour_C1:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes ab: "a \<le> b" and cd: "c \<le> d"
    and C1: "green_rectangle_C1 P Q a b c d"
  shows "(LINT p:{a..b} \<times> {c..d}|lborel.
      frechet_derivative Q (at p) (1,0) -
      frechet_derivative P (at p) (0,1)) =
    Re (contour_integral (rectpath (Complex a c) (Complex b d))
      (green_contour_coefficient P Q))"
proof -
  have P: "continuous_on ({a..b} \<times> {c..d}) P"
    by (rule green_rectangle_C1_continuous_on(1)[OF C1])
  have Q: "continuous_on ({a..b} \<times> {c..d}) Q"
    by (rule green_rectangle_C1_continuous_on(2)[OF C1])
  show ?thesis
    using Green_rectangle_four_edges_C1[OF ab cd C1]
      green_rectangle_contour_edges[OF ab cd P Q]
    by simp
qed

end
