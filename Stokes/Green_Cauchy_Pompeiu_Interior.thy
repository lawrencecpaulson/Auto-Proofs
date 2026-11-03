theory Green_Cauchy_Pompeiu_Interior
  imports Green_Cauchy_Pompeiu
begin

lemma green_cauchy_rectpath_kernel:
  assumes inside: "w \<in> box (Complex a c) (Complex b d)"
  shows "contour_integral (rectpath (Complex a c) (Complex b d))
      (\<lambda>z. 1 / (z - w)) = 2 * pi * \<i>"
proof -
  let ?g = "rectpath (Complex a c) (Complex b d)"
  have ab: "a < b" and cd: "c < d"
    using inside by (auto simp: in_box_complex_iff)
  have path: "path_image ?g =
      cbox (Complex a c) (Complex b d) -
        box (Complex a c) (Complex b d)"
    by (rule path_image_rectpath_cbox_minus_box)
      (use ab cd in simp_all)
  have away: "w \<notin> path_image ?g"
    using inside path by simp
  have wind: "winding_number ?g w = 1"
    by (rule winding_number_rectpath[OF inside])
  have eq: "winding_number ?g w = 1 / (2 * pi * \<i>) *
      contour_integral ?g (\<lambda>z. 1 / (z - w))"
    by (rule winding_number_valid_path[OF _ away])
      (simp add: rectpath_def Let_def)
  show ?thesis
    using wind eq
    by (simp add: field_simps)
qed

lemma green_rectpath_contour_edges:
  fixes f :: "complex \<Rightarrow> complex"
  assumes ab: "a < b" and cd: "c < d"
    and cont: "continuous_on
      (path_image (rectpath (Complex a c) (Complex b d))) f"
  shows "contour_integral
      (rectpath (Complex a c) (Complex b d)) f =
    contour_integral (linepath (Complex a c) (Complex b c)) f +
    contour_integral (linepath (Complex b c) (Complex b d)) f +
    contour_integral (linepath (Complex b d) (Complex a d)) f +
    contour_integral (linepath (Complex a d) (Complex a c)) f"
proof -
  let ?p1 = "Complex a c"
  let ?p2 = "Complex b c"
  let ?p3 = "Complex b d"
  let ?p4 = "Complex a d"
  let ?g = "rectpath ?p1 ?p3"
  have edge: "closed_segment p q \<subseteq> path_image ?g"
    if "(p,q) \<in> {(?p1,?p2), (?p2,?p3), (?p3,?p4), (?p4,?p1)}"
    for p q
    using that ab cd
    by (auto simp: path_image_rectpath closed_segment_same_Re
        closed_segment_same_Im closed_segment_eq_real_ivl)
  have cint: "f contour_integrable_on (linepath p q)"
    if "(p,q) \<in> {(?p1,?p2), (?p2,?p3), (?p3,?p4), (?p4,?p1)}"
    for p q
    by (rule contour_integrable_continuous_linepath)
      (rule continuous_on_subset[OF cont edge[OF that]])
  show ?thesis
    unfolding rectpath_def Let_def
    by (simp add: cint add.assoc)
qed

lemma green_contour_split_linepath_three:
  fixes f :: "complex \<Rightarrow> complex"
  assumes cont: "continuous_on (closed_segment A B) f"
    and Q: "Q \<in> closed_segment A B"
    and P: "P \<in> closed_segment A Q"
  shows "contour_integral (linepath A B) f =
    contour_integral (linepath A P) f +
    contour_integral (linepath P Q) f +
    contour_integral (linepath Q B) f"
proof -
  have sub: "closed_segment A Q \<subseteq> closed_segment A B"
    by (rule closed_segment_subset) (use Q in auto)
  have aq: "continuous_on (closed_segment A Q) f"
    by (rule continuous_on_subset[OF cont sub])
  have split1: "contour_integral (linepath A B) f =
    contour_integral (linepath A Q) f +
    contour_integral (linepath Q B) f"
    by (rule contour_integral_split_linepath[OF cont Q])
  have split2: "contour_integral (linepath A Q) f =
    contour_integral (linepath A P) f +
    contour_integral (linepath P Q) f"
    by (rule contour_integral_split_linepath[OF aq P])
  show ?thesis using split1 split2 by simp
qed

lemma green_contour_split_horizontal:
  fixes f :: "complex \<Rightarrow> complex"
  assumes ap: "a < p" and pq: "p < q" and qb: "q < b"
    and cont: "continuous_on
      (closed_segment (Complex a y) (Complex b y)) f"
  shows "contour_integral (linepath (Complex a y) (Complex b y)) f =
    contour_integral (linepath (Complex a y) (Complex p y)) f +
    contour_integral (linepath (Complex p y) (Complex q y)) f +
    contour_integral (linepath (Complex q y) (Complex b y)) f"
proof (rule green_contour_split_linepath_three[OF cont])
  show "Complex q y \<in>
    closed_segment (Complex a y) (Complex b y)"
    using ap pq qb
    by (auto simp: closed_segment_same_Im closed_segment_eq_real_ivl)
  show "Complex p y \<in>
    closed_segment (Complex a y) (Complex q y)"
    using ap pq
    by (auto simp: closed_segment_same_Im closed_segment_eq_real_ivl)
qed

lemma green_contour_split_vertical:
  fixes f :: "complex \<Rightarrow> complex"
  assumes cr: "c < r" and rs: "r < s" and sd: "s < d"
    and cont: "continuous_on
      (closed_segment (Complex x c) (Complex x d)) f"
  shows "contour_integral (linepath (Complex x c) (Complex x d)) f =
    contour_integral (linepath (Complex x c) (Complex x r)) f +
    contour_integral (linepath (Complex x r) (Complex x s)) f +
    contour_integral (linepath (Complex x s) (Complex x d)) f"
proof (rule green_contour_split_linepath_three[OF cont])
  show "Complex x s \<in>
    closed_segment (Complex x c) (Complex x d)"
    using cr rs sd
    by (auto simp: closed_segment_same_Re closed_segment_eq_real_ivl)
  show "Complex x r \<in>
    closed_segment (Complex x c) (Complex x s)"
    using cr rs
    by (auto simp: closed_segment_same_Re closed_segment_eq_real_ivl)
qed

lemma green_rectpath_contour_forward_edges:
  fixes f :: "complex \<Rightarrow> complex"
  assumes ab: "a < b" and cd: "c < d"
    and cont: "continuous_on
      (path_image (rectpath (Complex a c) (Complex b d))) f"
  shows "contour_integral
      (rectpath (Complex a c) (Complex b d)) f =
    contour_integral (linepath (Complex a c) (Complex b c)) f +
    contour_integral (linepath (Complex b c) (Complex b d)) f -
    contour_integral (linepath (Complex a d) (Complex b d)) f -
    contour_integral (linepath (Complex a c) (Complex a d)) f"
proof -
  have top: "continuous_on
      (closed_segment (Complex a d) (Complex b d)) f"
    by (rule continuous_on_subset[OF cont])
      (use ab cd in
        \<open>auto simp: path_image_rectpath closed_segment_same_Im
          closed_segment_eq_real_ivl\<close>)
  have left: "continuous_on
      (closed_segment (Complex a c) (Complex a d)) f"
    by (rule continuous_on_subset[OF cont])
      (use ab cd in
        \<open>auto simp: path_image_rectpath closed_segment_same_Re
          closed_segment_eq_real_ivl\<close>)
  have revtop: "contour_integral
      (linepath (Complex b d) (Complex a d)) f =
      - contour_integral (linepath (Complex a d) (Complex b d)) f"
    using contour_integral_reverse_linepath[OF top] by simp
  have revleft: "contour_integral
      (linepath (Complex a d) (Complex a c)) f =
      - contour_integral (linepath (Complex a c) (Complex a d)) f"
    using contour_integral_reverse_linepath[OF left] by simp
  show ?thesis
    using green_rectpath_contour_edges[OF ab cd cont] revtop revleft
    by simp
qed

lemma green_rectangle_ring_boundary_algebra:
  fixes H V :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex"
  assumes Hc: "H a b c = H a p c + H p q c + H q b c"
    and Hd: "H a b d = H a p d + H p q d + H q b d"
    and Va: "V c d a = V c r a + V r s a + V s d a"
    and Vb: "V c d b = V c r b + V r s b + V s d b"
    and Vp: "V c d p = V c r p + V r s p + V s d p"
    and Vq: "V c d q = V c r q + V r s q + V s d q"
  shows "(H a b c + V c d b - H a b d - V c d a) =
    (H a p c + V c d p - H a p d - V c d a) +
    (H q b c + V c d b - H q b d - V c d q) +
    (H p q c + V c r q - H p q r - V c r p) +
    (H p q s + V s d q - H p q d - V s d p) +
    (H p q r + V r s q - H p q s - V r s p)"
  using assms by (simp add: algebra_simps)

lemma green_rectpath_punctured_contour:
  fixes f :: "complex \<Rightarrow> complex"
  assumes ap: "a < p" and pq: "p < q" and qb: "q < b"
    and cr: "c < r" and rs: "r < s" and sd: "s < d"
    and cont: "continuous_on
      (cbox (Complex a c) (Complex b d) -
        box (Complex p r) (Complex q s)) f"
  shows "contour_integral (rectpath (Complex a c) (Complex b d)) f =
    contour_integral (rectpath (Complex a c) (Complex p d)) f +
    contour_integral (rectpath (Complex q c) (Complex b d)) f +
    contour_integral (rectpath (Complex p c) (Complex q r)) f +
    contour_integral (rectpath (Complex p s) (Complex q d)) f +
    contour_integral (rectpath (Complex p r) (Complex q s)) f"
proof -
  let ?S = "cbox (Complex a c) (Complex b d) -
    box (Complex p r) (Complex q s)"
  let ?H = "\<lambda>x y z. contour_integral
    (linepath (Complex x z) (Complex y z)) f"
  let ?V = "\<lambda>x y z. contour_integral
    (linepath (Complex z x) (Complex z y)) f"
  have ab: "a < b" and cd: "c < d"
    using ap pq qb cr rs sd by auto
  have inner_outer: "box (Complex p r) (Complex q s) \<subseteq>
      box (Complex a c) (Complex b d)"
    using ap pq qb cr rs sd
    by (auto simp: in_box_complex_iff)
  have outerP: "path_image
      (rectpath (Complex a c) (Complex b d)) \<subseteq> ?S"
    using path_image_rectpath_subset_cbox[of "Complex a c" "Complex b d"]
      path_image_rectpath_inter_box[of "Complex a c" "Complex b d"]
      inner_outer ab cd by auto
  have innerP: "path_image
      (rectpath (Complex p r) (Complex q s)) \<subseteq> ?S"
  proof -
    have sub: "cbox (Complex p r) (Complex q s) \<subseteq>
        cbox (Complex a c) (Complex b d)"
      using ap pq qb cr rs sd
      by (auto simp: in_cbox_complex_iff)
    show ?thesis
      using path_image_rectpath_subset_cbox[of "Complex p r" "Complex q s"]
        path_image_rectpath_inter_box[of "Complex p r" "Complex q s"]
        sub pq rs by auto
  qed
  have leftS: "cbox (Complex a c) (Complex p d) \<subseteq> ?S"
    using ap pq qb cr rs sd
    by (auto simp: in_cbox_complex_iff in_box_complex_iff)
  have rightS: "cbox (Complex q c) (Complex b d) \<subseteq> ?S"
    using ap pq qb cr rs sd
    by (auto simp: in_cbox_complex_iff in_box_complex_iff)
  have bottomS: "cbox (Complex p c) (Complex q r) \<subseteq> ?S"
    using ap pq qb cr rs sd
    by (auto simp: in_cbox_complex_iff in_box_complex_iff)
  have topS: "cbox (Complex p s) (Complex q d) \<subseteq> ?S"
    using ap pq qb cr rs sd
    by (auto simp: in_cbox_complex_iff in_box_complex_iff)
  have c_outer: "continuous_on
      (path_image (rectpath (Complex a c) (Complex b d))) f"
    by (rule continuous_on_subset[OF cont outerP])
  have c_inner: "continuous_on
      (path_image (rectpath (Complex p r) (Complex q s))) f"
    by (rule continuous_on_subset[OF cont innerP])
  have c_left: "continuous_on
      (path_image (rectpath (Complex a c) (Complex p d))) f"
    by (rule continuous_on_subset[OF cont])
      (rule subset_trans[OF path_image_rectpath_subset_cbox leftS];
        use ap cd in simp_all)
  have c_right: "continuous_on
      (path_image (rectpath (Complex q c) (Complex b d))) f"
    by (rule continuous_on_subset[OF cont])
      (rule subset_trans[OF path_image_rectpath_subset_cbox rightS];
        use qb cd in simp_all)
  have c_bottom: "continuous_on
      (path_image (rectpath (Complex p c) (Complex q r))) f"
    by (rule continuous_on_subset[OF cont])
      (rule subset_trans[OF path_image_rectpath_subset_cbox bottomS];
        use pq cr in simp_all)
  have c_top: "continuous_on
      (path_image (rectpath (Complex p s) (Complex q d))) f"
    by (rule continuous_on_subset[OF cont])
      (rule subset_trans[OF path_image_rectpath_subset_cbox topS];
        use pq sd in simp_all)
  have Hcont: "continuous_on
      (closed_segment (Complex a y) (Complex b y)) f"
    if "y \<in> {c,d}" for y
    by (rule continuous_on_subset[OF cont])
      (use that ap pq qb cr rs sd in
        \<open>auto simp: closed_segment_same_Im
          closed_segment_eq_real_ivl
          in_cbox_complex_iff in_box_complex_iff\<close>)
  have Vcont: "continuous_on
      (closed_segment (Complex x c) (Complex x d)) f"
    if "x \<in> {a,b,p,q}" for x
    by (rule continuous_on_subset[OF cont])
      (use that ap pq qb cr rs sd in
        \<open>auto simp: closed_segment_same_Re
          closed_segment_eq_real_ivl
          in_cbox_complex_iff in_box_complex_iff\<close>)
  have Hc: "?H a b c = ?H a p c + ?H p q c + ?H q b c"
    by (rule green_contour_split_horizontal[OF ap pq qb Hcont])
      simp
  have Hd: "?H a b d = ?H a p d + ?H p q d + ?H q b d"
    by (rule green_contour_split_horizontal[OF ap pq qb Hcont])
      simp
  have Vsplit: "?V c d x = ?V c r x + ?V r s x + ?V s d x"
    if "x \<in> {a,b,p,q}" for x
    by (rule green_contour_split_vertical[OF cr rs sd Vcont[OF that]])
  have algebra:
    "(?H a b c + ?V c d b - ?H a b d - ?V c d a) =
      (?H a p c + ?V c d p - ?H a p d - ?V c d a) +
      (?H q b c + ?V c d b - ?H q b d - ?V c d q) +
      (?H p q c + ?V c r q - ?H p q r - ?V c r p) +
      (?H p q s + ?V s d q - ?H p q d - ?V s d p) +
      (?H p q r + ?V r s q - ?H p q s - ?V r s p)"
    by (rule green_rectangle_ring_boundary_algebra
      [OF Hc Hd Vsplit[of a] Vsplit[of b]
        Vsplit[of p] Vsplit[of q]])
      simp_all
  have outerE: "contour_integral
      (rectpath (Complex a c) (Complex b d)) f =
      ?H a b c + ?V c d b - ?H a b d - ?V c d a"
    by (rule green_rectpath_contour_forward_edges[OF ab cd c_outer])
  have leftE: "contour_integral
      (rectpath (Complex a c) (Complex p d)) f =
      ?H a p c + ?V c d p - ?H a p d - ?V c d a"
    by (rule green_rectpath_contour_forward_edges[OF ap cd c_left])
  have rightE: "contour_integral
      (rectpath (Complex q c) (Complex b d)) f =
      ?H q b c + ?V c d b - ?H q b d - ?V c d q"
    by (rule green_rectpath_contour_forward_edges[OF qb cd c_right])
  have bottomE: "contour_integral
      (rectpath (Complex p c) (Complex q r)) f =
      ?H p q c + ?V c r q - ?H p q r - ?V c r p"
    by (rule green_rectpath_contour_forward_edges[OF pq cr c_bottom])
  have topE: "contour_integral
      (rectpath (Complex p s) (Complex q d)) f =
      ?H p q s + ?V s d q - ?H p q d - ?V s d p"
    by (rule green_rectpath_contour_forward_edges[OF pq sd c_top])
  have innerE: "contour_integral
      (rectpath (Complex p r) (Complex q s)) f =
      ?H p q r + ?V r s q - ?H p q s - ?V r s p"
    by (rule green_rectpath_contour_forward_edges[OF pq rs c_inner])
  show ?thesis
    using algebra outerE leftE rightE bottomE topE innerE by simp
qed

definition green_puncture_cells ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
    real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
    green_rectangle set" where
  "green_puncture_cells a b c d p q r s =
    {(Complex a c, Complex p d),
     (Complex q c, Complex b d),
     (Complex p c, Complex q r),
     (Complex p s, Complex q d),
     (Complex p r, Complex q s)}"

lemma green_puncture_cells_division:
  assumes ap: "a < p" and pq: "p < q" and qb: "q < b"
    and cr: "c < r" and rs: "r < s" and sd: "s < d"
  shows "green_rectangular_division
    (green_puncture_cells a b c d p q r s)"
  using assms
  by (auto simp: green_rectangular_division_def
      green_puncture_cells_def green_rectangle_open_def box_prod)

lemma green_puncture_cells_region:
  assumes ap: "a < p" and pq: "p < q" and qb: "q < b"
    and cr: "c < r" and rs: "r < s" and sd: "s < d"
  shows "green_rectangular_region
      (green_puncture_cells a b c d p q r s) =
    {a..b} \<times> {c..d}"
  using assms
  by (auto simp: green_rectangular_region_def
      green_puncture_cells_def green_rectangle_set_def cbox_Pair_eq)

lemma green_puncture_cells_area:
  fixes f :: "real \<times> real \<Rightarrow> complex"
  assumes ap: "a < p" and pq: "p < q" and qb: "q < b"
    and cr: "c < r" and rs: "r < s" and sd: "s < d"
    and fint: "set_integrable lborel ({a..b} \<times> {c..d}) f"
  shows "(LINT z:{a..b} \<times> {c..d}|lborel. f z) =
    (LINT z:{a..p} \<times> {c..d}|lborel. f z) +
    (LINT z:{q..b} \<times> {c..d}|lborel. f z) +
    (LINT z:{p..q} \<times> {c..r}|lborel. f z) +
    (LINT z:{p..q} \<times> {s..d}|lborel. f z) +
    (LINT z:{p..q} \<times> {r..s}|lborel. f z)"
proof -
  let ?R = "green_puncture_cells a b c d p q r s"
  have div: "green_rectangular_division ?R"
    by (rule green_puncture_cells_division[OF ap pq qb cr rs sd])
  have region: "green_rectangular_region ?R = {a..b} \<times> {c..d}"
    by (rule green_puncture_cells_region[OF ap pq qb cr rs sd])
  have finite: "finite ?R"
    using div by (simp add: green_rectangular_division_def)
  have intcell: "set_integrable lborel (green_rectangle_set t) f"
    if "t \<in> ?R" for t
  proof (rule set_integrable_subset[OF fint])
    show "green_rectangle_set t \<in> sets lborel"
      by (simp add: green_rectangle_set_def)
    show "green_rectangle_set t \<subseteq> {a..b} \<times> {c..d}"
      using that region
      by (auto simp: green_rectangular_region_def)
  qed
  have area: "(LINT z:{a..b} \<times> {c..d}|lborel. f z) =
      (\<Sum>t\<in>?R. LINT z:green_rectangle_set t|lborel. f z)"
    unfolding region[symmetric] green_rectangular_region_def
  proof (rule set_integral_finite_UN_AE[OF finite])
    fix t v
    assume "t \<in> ?R" "v \<in> ?R"
    then show "AE z in lborel.
        (z \<in> green_rectangle_set t \<and>
          z \<in> green_rectangle_set v) \<longrightarrow> t = v"
      by (rule green_rectangular_ae_disjoint[OF div])
  next
    fix t
    assume "t \<in> ?R"
    then show "green_rectangle_set t \<in> sets lborel"
      by (simp add: green_rectangle_set_def)
  next
    fix t
    assume "t \<in> ?R"
    then show "set_integrable lborel (green_rectangle_set t) f"
      by (rule intcell)
  qed
  show ?thesis
    using area ap pq qb cr rs sd
    by (simp add: green_puncture_cells_def
      green_rectangle_set_def cbox_Pair_eq)
qed

lemma green_cauchy_punctured_rectangle:
  fixes u :: "complex \<Rightarrow> complex"
  assumes ap: "a < p" and pq: "p < q" and qb: "q < b"
    and cr: "c < r" and rs: "r < s" and sd: "s < d"
    and C1: "Ck_on 1 u V"
    and rect: "cbox (Complex a c) (Complex b d) \<subseteq> V"
    and inside: "w \<in> box (Complex p r) (Complex q s)"
    and fint: "set_integrable lborel ({a..b} \<times> {c..d})
      (\<lambda>t. green_wirtinger_dbar u (green_complex_of_pair t) /
        (green_complex_of_pair t - w))"
  shows "contour_integral
      (rectpath (Complex a c) (Complex b d))
      (\<lambda>z. u z / (z - w)) =
    contour_integral
      (rectpath (Complex p r) (Complex q s))
      (\<lambda>z. u z / (z - w)) +
    2 * \<i> * ((LINT t:{a..b} \<times> {c..d}|lborel.
      green_wirtinger_dbar u (green_complex_of_pair t) /
        (green_complex_of_pair t - w)) -
      (LINT t:{p..q} \<times> {r..s}|lborel.
      green_wirtinger_dbar u (green_complex_of_pair t) /
        (green_complex_of_pair t - w)))"
proof -
  let ?f = "\<lambda>z. u z / (z - w)"
  let ?F = "\<lambda>t. green_wirtinger_dbar u (green_complex_of_pair t) /
    (green_complex_of_pair t - w)"
  let ?S = "cbox (Complex a c) (Complex b d) -
    box (Complex p r) (Complex q s)"
  have ab: "a < b" and cd: "c < d"
    using ap pq qb cr rs sd by auto
  have uc: "continuous_on V u"
    by (rule Ck_on_imp_continuous_on[OF C1])
  have openV: "open V" by (rule Ck_on_open[OF C1])
  have fc: "continuous_on (V - {w}) ?f"
    by (intro continuous_intros continuous_on_subset[OF uc]) auto
  have Sc: "continuous_on ?S ?f"
    by (rule continuous_on_subset[OF fc]) (use rect inside in auto)
  have contour: "contour_integral
      (rectpath (Complex a c) (Complex b d)) ?f =
      contour_integral (rectpath (Complex a c) (Complex p d)) ?f +
      contour_integral (rectpath (Complex q c) (Complex b d)) ?f +
      contour_integral (rectpath (Complex p c) (Complex q r)) ?f +
      contour_integral (rectpath (Complex p s) (Complex q d)) ?f +
      contour_integral (rectpath (Complex p r) (Complex q s)) ?f"
    by (rule green_rectpath_punctured_contour
      [OF ap pq qb cr rs sd Sc])
  have area: "(LINT t:{a..b} \<times> {c..d}|lborel. ?F t) =
      (LINT t:{a..p} \<times> {c..d}|lborel. ?F t) +
      (LINT t:{q..b} \<times> {c..d}|lborel. ?F t) +
      (LINT t:{p..q} \<times> {c..r}|lborel. ?F t) +
      (LINT t:{p..q} \<times> {s..d}|lborel. ?F t) +
      (LINT t:{p..q} \<times> {r..s}|lborel. ?F t)"
    by (rule green_puncture_cells_area
      [OF ap pq qb cr rs sd fint])
  have ex_left: "contour_integral
      (rectpath (Complex a c) (Complex p d)) ?f =
      2 * \<i> * (LINT t:{a..p} \<times> {c..d}|lborel. ?F t)"
    by (rule green_cauchy_rectangle_exterior[OF _ _ C1])
      (use ap pq qb cr rs sd rect inside in
        \<open>auto simp: in_cbox_complex_iff in_box_complex_iff\<close>)
  have ex_right: "contour_integral
      (rectpath (Complex q c) (Complex b d)) ?f =
      2 * \<i> * (LINT t:{q..b} \<times> {c..d}|lborel. ?F t)"
    by (rule green_cauchy_rectangle_exterior[OF _ _ C1])
      (use ap pq qb cr rs sd rect inside in
        \<open>auto simp: in_cbox_complex_iff in_box_complex_iff\<close>)
  have ex_bottom: "contour_integral
      (rectpath (Complex p c) (Complex q r)) ?f =
      2 * \<i> * (LINT t:{p..q} \<times> {c..r}|lborel. ?F t)"
    by (rule green_cauchy_rectangle_exterior[OF _ _ C1])
      (use ap pq qb cr rs sd rect inside in
        \<open>auto simp: in_cbox_complex_iff in_box_complex_iff\<close>)
  have ex_top: "contour_integral
      (rectpath (Complex p s) (Complex q d)) ?f =
      2 * \<i> * (LINT t:{p..q} \<times> {s..d}|lborel. ?F t)"
    by (rule green_cauchy_rectangle_exterior[OF _ _ C1])
      (use ap pq qb cr rs sd rect inside in
        \<open>auto simp: in_cbox_complex_iff in_box_complex_iff\<close>)
  show ?thesis
    using contour area ex_left ex_right ex_bottom ex_top
    by (simp add: algebra_simps)
qed

lemma green_rectpath_four_segments:
  "path_image (rectpath (Complex a c) (Complex b d)) =
    closed_segment (Complex a c) (Complex b c) \<union>
    closed_segment (Complex b c) (Complex b d) \<union>
    closed_segment (Complex b d) (Complex a d) \<union>
    closed_segment (Complex a d) (Complex a c)"
  by (simp add: rectpath_def Let_def path_image_join Un_assoc)

lemma green_rectpath_contour_bound:
  fixes f :: "complex \<Rightarrow> complex"
  assumes ab: "a < b" and cd: "c < d"
    and cont: "continuous_on
      (path_image (rectpath (Complex a c) (Complex b d))) f"
    and B: "0 \<le> B"
    and bound: "\<And>z. z \<in> path_image
      (rectpath (Complex a c) (Complex b d)) \<Longrightarrow> norm (f z) \<le> B"
  shows "norm (contour_integral
      (rectpath (Complex a c) (Complex b d)) f) \<le>
    2 * B * ((b - a) + (d - c))"
proof -
  let ?p1 = "Complex a c"
  let ?p2 = "Complex b c"
  let ?p3 = "Complex b d"
  let ?p4 = "Complex a d"
  let ?g = "rectpath ?p1 ?p3"
  let ?i1 = "contour_integral (linepath ?p1 ?p2) f"
  let ?i2 = "contour_integral (linepath ?p2 ?p3) f"
  let ?i3 = "contour_integral (linepath ?p3 ?p4) f"
  let ?i4 = "contour_integral (linepath ?p4 ?p1) f"
  have path: "path_image ?g =
      closed_segment ?p1 ?p2 \<union>
      closed_segment ?p2 ?p3 \<union>
      closed_segment ?p3 ?p4 \<union>
      closed_segment ?p4 ?p1"
    by (rule green_rectpath_four_segments)
  have cint: "f contour_integrable_on (linepath x y)"
    if "(x,y) \<in> {(?p1,?p2), (?p2,?p3), (?p3,?p4), (?p4,?p1)}"
    for x y
    by (rule contour_integrable_continuous_linepath)
      (rule continuous_on_subset[OF cont]; use that path in auto)
  have bnd: "norm (contour_integral (linepath x y) f) \<le>
      B * norm (y - x)"
    if "(x,y) \<in> {(?p1,?p2), (?p2,?p3), (?p3,?p4), (?p4,?p1)}"
    for x y
    by (rule contour_integral_bound_linepath[OF cint[OF that] B])
      (use bound that path in auto)
  have b1: "norm ?i1 \<le> B * (b - a)"
    using bnd[of ?p1 ?p2] ab
    by (simp add: complex_diff complex_norm)
  have b2: "norm ?i2 \<le> B * (d - c)"
    using bnd[of ?p2 ?p3] cd
    by (simp add: complex_diff complex_norm)
  have b3: "norm ?i3 \<le> B * (b - a)"
    using bnd[of ?p3 ?p4] ab
    by (simp add: complex_diff complex_norm)
  have b4: "norm ?i4 \<le> B * (d - c)"
    using bnd[of ?p4 ?p1] cd
    by (simp add: complex_diff complex_norm)
  have edge: "contour_integral ?g f = ?i1 + ?i2 + ?i3 + ?i4"
    by (rule green_rectpath_contour_edges[OF ab cd cont])
  have triangle: "norm (?i1 + ?i2 + ?i3 + ?i4) \<le>
      norm ?i1 + norm ?i2 + norm ?i3 + norm ?i4"
    by (smt (verit) norm_triangle_ineq)
  show ?thesis
    unfolding edge
    using triangle b1 b2 b3 b4 by (simp add: algebra_simps)
qed

lemma green_complex_norm_le_components:
  "norm (Complex x y) \<le> \<bar>x\<bar> + \<bar>y\<bar>"
proof -
  have eq: "Complex x y = Complex x 0 + Complex 0 y"
    by (simp add: complex_add)
  have "norm (Complex x 0 + Complex 0 y) \<le>
      norm (Complex x 0) + norm (Complex 0 y)"
    by (rule norm_triangle_ineq)
  then show ?thesis by (simp add: eq[symmetric] complex_norm)
qed

lemma green_square_path_distance:
  fixes e :: real
  assumes e: "0 < e"
    and z: "z \<in> path_image
      (rectpath (Complex (x - e) (y - e))
        (Complex (x + e) (y + e)))"
  shows "e \<le> norm (z - Complex x y)"
    and "norm (z - Complex x y) \<le> 2 * e"
proof -
  have bounds: "x - e \<le> Re z" "Re z \<le> x + e"
    "y - e \<le> Im z" "Im z \<le> y + e"
    using z e
    by (auto simp: path_image_rectpath)
  have side: "Re z = x - e \<or> Re z = x + e \<or>
      Im z = y - e \<or> Im z = y + e"
    using z e
    by (auto simp: path_image_rectpath)
  have diff: "z - Complex x y =
      Complex (Re z - x) (Im z - y)"
    by (simp add: complex_eq_iff)
  have lower_Re: "\<bar>Re z - x\<bar> \<le> norm (z - Complex x y)"
    using abs_Re_le_cmod[of "z - Complex x y"] by simp
  have lower_Im: "\<bar>Im z - y\<bar> \<le> norm (z - Complex x y)"
    using abs_Im_le_cmod[of "z - Complex x y"] by simp
  show "e \<le> norm (z - Complex x y)"
    using side e lower_Re lower_Im by auto
  have upper: "norm (z - Complex x y) \<le>
      \<bar>Re z - x\<bar> + \<bar>Im z - y\<bar>"
    unfolding diff by (rule green_complex_norm_le_components)
  show "norm (z - Complex x y) \<le> 2 * e"
    using bounds upper by linarith
qed

lemma green_rectpath_contour_integrable:
  fixes f :: "complex \<Rightarrow> complex"
  assumes cont: "continuous_on
    (path_image (rectpath (Complex a c) (Complex b d))) f"
  shows "f contour_integrable_on
    (rectpath (Complex a c) (Complex b d))"
proof -
  let ?p1 = "Complex a c"
  let ?p2 = "Complex b c"
  let ?p3 = "Complex b d"
  let ?p4 = "Complex a d"
  have path: "path_image (rectpath ?p1 ?p3) =
      closed_segment ?p1 ?p2 \<union>
      closed_segment ?p2 ?p3 \<union>
      closed_segment ?p3 ?p4 \<union>
      closed_segment ?p4 ?p1"
    by (rule green_rectpath_four_segments)
  have cint: "f contour_integrable_on (linepath x y)"
    if "(x,y) \<in> {(?p1,?p2), (?p2,?p3), (?p3,?p4), (?p4,?p1)}"
    for x y
    by (rule contour_integrable_continuous_linepath)
      (rule continuous_on_subset[OF cont]; use that path in auto)
  show ?thesis
    unfolding rectpath_def Let_def by (simp add: cint)
qed

lemma green_square_contour_remainder_bound:
  fixes e delta :: real
  assumes e: "0 < e" and delta: "0 \<le> delta"
    and uc: "continuous_on
      (path_image (rectpath
        (Complex (x - e) (y - e))
        (Complex (x + e) (y + e)))) u"
    and near: "\<And>z. z \<in> path_image (rectpath
      (Complex (x - e) (y - e))
      (Complex (x + e) (y + e))) \<Longrightarrow>
      norm (u z - u (Complex x y)) \<le> delta"
  shows "norm (contour_integral
      (rectpath (Complex (x - e) (y - e))
        (Complex (x + e) (y + e)))
      (\<lambda>z. (u z - u (Complex x y)) /
        (z - Complex x y))) \<le> 8 * delta"
proof -
  let ?w = "Complex x y"
  let ?g = "rectpath
    (Complex (x - e) (y - e))
    (Complex (x + e) (y + e))"
  let ?f = "\<lambda>z. (u z - u ?w) / (z - ?w)"
  have low: "e \<le> norm (z - ?w)" if "z \<in> path_image ?g" for z
    by (rule green_square_path_distance(1)[OF e that])
  have neq: "z \<noteq> ?w" if "z \<in> path_image ?g" for z
    using low[OF that] e by auto
  have fc: "continuous_on (path_image ?g) ?f"
    by (intro continuous_intros uc)
      (use neq in auto)
  have point: "norm (?f z) \<le> delta / e"
    if z: "z \<in> path_image ?g" for z
  proof -
    have lo: "0 < norm (z - ?w)" using low[OF z] e by linarith
    have le: "norm (u z - u ?w) * e \<le>
        delta * norm (z - ?w)"
    proof -
      have first: "norm (u z - u ?w) * e \<le> delta * e"
        by (rule mult_right_mono[OF near[OF z]]) (use e in auto)
      have second: "delta * e \<le> delta * norm (z - ?w)"
        by (rule mult_left_mono[OF low[OF z] delta])
      show ?thesis using first second by linarith
    qed
    show ?thesis
      using le lo e
      by (simp add: norm_divide field_simps)
  qed
  have bound: "norm (contour_integral ?g ?f) \<le>
      2 * (delta / e) *
        (((x + e) - (x - e)) + ((y + e) - (y - e)))"
    by (rule green_rectpath_contour_bound[OF _ _ fc])
      (use e delta point in auto)
  show ?thesis using bound e by (simp add: field_simps)
qed

lemma green_square_contour_decomposition:
  fixes e :: real and u :: "complex \<Rightarrow> complex"
  assumes e: "0 < e"
    and uc: "continuous_on
      (path_image (rectpath
        (Complex (x - e) (y - e))
        (Complex (x + e) (y + e)))) u"
  shows "contour_integral
      (rectpath (Complex (x - e) (y - e))
        (Complex (x + e) (y + e)))
      (\<lambda>z. u z / (z - Complex x y)) -
    2 * pi * \<i> * u (Complex x y) =
    contour_integral
      (rectpath (Complex (x - e) (y - e))
        (Complex (x + e) (y + e)))
      (\<lambda>z. (u z - u (Complex x y)) /
        (z - Complex x y))"
proof -
  let ?w = "Complex x y"
  let ?g = "rectpath
    (Complex (x - e) (y - e))
    (Complex (x + e) (y + e))"
  let ?K = "\<lambda>z. 1 / (z - ?w)"
  let ?F = "\<lambda>z. u z / (z - ?w)"
  let ?G = "\<lambda>z. (u z - u ?w) / (z - ?w)"
  have away: "z \<noteq> ?w" if "z \<in> path_image ?g" for z
    using green_square_path_distance(1)[OF e that] e by auto
  have Kcont: "continuous_on (path_image ?g) ?K"
    by (intro continuous_intros) (use away in auto)
  have Fcont: "continuous_on (path_image ?g) ?F"
    by (intro continuous_intros uc) (use away in auto)
  have Kint: "?K contour_integrable_on ?g"
    by (rule green_rectpath_contour_integrable[OF Kcont])
  have Fint: "?F contour_integrable_on ?g"
    by (rule green_rectpath_contour_integrable[OF Fcont])
  have G: "?G = (\<lambda>z. ?F z - u ?w * ?K z)"
    by (rule ext) (simp add: diff_divide_distrib divide_inverse algebra_simps)
  have wind: "contour_integral ?g ?K = 2 * pi * \<i>"
    by (rule green_cauchy_rectpath_kernel)
      (use e in \<open>auto simp: in_box_complex_iff\<close>)
  have "contour_integral ?g ?G =
      contour_integral ?g ?F - u ?w * contour_integral ?g ?K"
    unfolding G
    by (subst contour_integral_diff[OF Fint
      contour_integrable_lmul[OF Kint]])
      (simp add: contour_integral_lmul divide_inverse)
  then show ?thesis using wind by (simp add: algebra_simps)
qed

definition green_cauchy_square_path :: "complex \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex" where
  "green_cauchy_square_path w e =
    rectpath (Complex (Re w - e) (Im w - e))
      (Complex (Re w + e) (Im w + e))"

lemma green_cauchy_square_contour_limit:
  fixes u :: "complex \<Rightarrow> complex"
  assumes C1: "Ck_on 1 u V" and wV: "w \<in> V"
  shows "((\<lambda>e. contour_integral (green_cauchy_square_path w e)
      (\<lambda>z. u z / (z - w))) \<longlongrightarrow>
    2 * pi * \<i> * u w) (at_right 0)"
proof -
  have openV: "open V" by (rule Ck_on_open[OF C1])
  have uc: "continuous_on V u"
    by (rule Ck_on_imp_continuous_on[OF C1])
  have uat: "continuous (at w) u"
    using uc openV wV
    by (simp add: continuous_on_eq_continuous_at)
  obtain R where R: "0 < R" "cball w R \<subseteq> V"
    using openV wV by (meson open_contains_cball)
  show ?thesis
    unfolding tendsto_iff
  proof (intro allI impI)
    fix eta :: real
    assume eta: "0 < eta"
    obtain d where d: "0 < d"
      and une: "\<And>z. norm (z - w) < d \<Longrightarrow>
        norm (u z - u w) < eta / 16"
      using uat[unfolded continuous_at_eps_delta, rule_format,
        of "eta / 16"] eta
      by (auto simp: dist_norm)
    have ev: "eventually
        (\<lambda>e::real. 0 < e \<and> e < min (R / 2) (d / 2))
        (at_right 0)"
      using R(1) d
      unfolding eventually_at_right_field
      by (intro exI[where x="min (R / 2) (d / 2)"]) auto
    show "eventually
      (\<lambda>e. dist
        (contour_integral (green_cauchy_square_path w e)
          (\<lambda>z. u z / (z - w)))
        (2 * pi * \<i> * u w) < eta) (at_right 0)"
    using ev
    proof eventually_elim
      case (elim e)
      let ?g = "green_cauchy_square_path w e"
      have e: "0 < e" and eR: "2 * e < R"
        and ed: "2 * e < d"
        using elim by auto
      have small: "norm (z - w) \<le> 2 * e"
        if z: "z \<in> path_image ?g" for z
        using green_square_path_distance(2)
          [OF e, of z "Re w" "Im w"] z
        by (simp add: green_cauchy_square_path_def)
      have pathV: "path_image ?g \<subseteq> V"
      proof
        fix z
        assume z: "z \<in> path_image ?g"
        have "z \<in> cball w R"
          using small[OF z] eR
          by (simp add: dist_norm norm_minus_commute; linarith)
        then show "z \<in> V" using R(2) by blast
      qed
      have ucg: "continuous_on (path_image ?g) u"
        by (rule continuous_on_subset[OF uc pathV])
      have near: "norm (u z - u w) \<le> eta / 16"
        if z: "z \<in> path_image ?g" for z
        using une[of z] small[OF z] ed by linarith
      have rem: "norm (contour_integral ?g
          (\<lambda>z. (u z - u w) / (z - w))) \<le>
        8 * (eta / 16)"
        using green_square_contour_remainder_bound
          [where e=e and delta="eta / 16" and x="Re w"
            and y="Im w" and u=u] e eta ucg near
        by (simp add: green_cauchy_square_path_def)
      have decomp: "contour_integral ?g
          (\<lambda>z. u z / (z - w)) -
        2 * pi * \<i> * u w =
        contour_integral ?g
          (\<lambda>z. (u z - u w) / (z - w))"
        using green_square_contour_decomposition
          [where e=e and x="Re w" and y="Im w" and u=u]
          e ucg
        by (simp add: green_cauchy_square_path_def)
      have distance: "dist (contour_integral ?g
          (\<lambda>z. u z / (z - w))) (2 * pi * \<i> * u w) =
        norm (contour_integral ?g
          (\<lambda>z. (u z - u w) / (z - w)))"
        by (simp only: dist_norm decomp)
      have half: "norm (contour_integral ?g
          (\<lambda>z. (u z - u w) / (z - w))) \<le> eta / 2"
        using rem by simp
      show ?case using distance half eta by linarith
    qed
  qed
qed


lemma green_cauchy_density_integrable_cbox:
  fixes h :: "complex \<Rightarrow> complex"
  assumes hc: "continuous_on (cbox A B) h"
  shows "set_integrable (lborel :: complex measure) (cbox A B)
    (\<lambda>z. h z / (z - w))"
proof -
  let ?S = "cbox A B"
  have compact: "compact ?S" by simp
  have bounded: "bounded ?S" by (rule compact_imp_bounded[OF compact])
  obtain R where R: "\<And>z. z \<in> ?S \<Longrightarrow> dist w z \<le> R"
    using bounded unfolding bounded_any_center[where a=w] by blast
  let ?T = "max R 0"
  have sub: "?S \<subseteq> cball w ?T"
    using R by (auto simp: dist_commute) force
  have T: "0 \<le> ?T" by simp
  have hbdd: "bounded (h ` ?S)"
    by (rule compact_imp_bounded)
      (rule compact_continuous_image[OF hc compact])
  obtain C where C: "\<And>z. z \<in> ?S \<Longrightarrow> norm (h z) \<le> C"
    using hbdd unfolding bounded_iff by blast
  let ?K = "\<lambda>z. indicator ?S z *\<^sub>R (h z / (z - w))"
  let ?H = "\<lambda>z::complex. indicator (cball w ?T) z *\<^sub>R
    (1 / norm (z - w))"
  have Hint: "integrable lborel ?H"
    by (rule green_inverse_distance_integrable_cball[OF T])
  have maj: "integrable lborel (\<lambda>z. max C 0 * ?H z)"
    by (rule Bochner_Integration.integrable_mult_right[OF Hint])
  have Kmeas: "?K \<in> borel_measurable (lborel :: complex measure)"
  proof -
    have hc': "continuous_on (?S - {w}) (\<lambda>z. h z / (z-w))"
      by (intro continuous_intros continuous_on_subset[OF hc]) auto
    have eq: "?K z = indicator (?S - {w}) z *\<^sub>R (h z / (z-w))" for z
      by (auto simp: indicator_def)
    have B: "?S - {w} \<in> sets borel" by simp
    have M: "(\<lambda>z. indicator (?S - {w}) z *\<^sub>R (h z / (z-w)))
      \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_on_indicator[OF B hc'])
    show ?thesis using M by (simp add: eq)
  qed
  have bound: "norm (?K z) \<le> norm (max C 0 * ?H z)" for z
  proof (cases "z \<in> ?S")
    case True
    then have H: "?H z = 1 / norm (z-w)"
      using sub True by (auto simp: indicator_def)
    have "norm (h z / (z-w)) \<le> max C 0 * (1 / norm (z-w))"
      proof -
        have le: "norm (h z) \<le> max C 0" using C[OF True] by simp
        have nn: "0 \<le> inverse (norm (z-w))" by simp
        have "norm (h z) * inverse (norm (z-w)) \<le>
          max C 0 * inverse (norm (z-w))"
          by (rule mult_right_mono[OF le nn])
        then show ?thesis by (simp add: norm_divide norm_mult norm_inverse divide_inverse)
      qed
    then show ?thesis using True sub by (auto simp: indicator_def norm_mult)
  next
    case False
    then show ?thesis using T by (simp add: indicator_def)
  qed
  show ?thesis
    unfolding set_integrable_def
    by (rule Bochner_Integration.integrable_bound[OF maj Kmeas])
      (rule AE_I2[OF bound])
qed

lemma green_cauchy_pair_integrable_cbox:
  fixes h :: "complex \<Rightarrow> complex"
  assumes hc: "continuous_on (cbox (Complex a c) (Complex b d)) h"
  shows "set_integrable (lborel :: (real \<times> real) measure)
    ({a..b} \<times> {c..d})
    (\<lambda>p. h (green_complex_of_pair p) /
      (green_complex_of_pair p - w))"
proof -
  let ?E = green_complex_of_pair
  let ?S = "cbox (Complex a c) (Complex b d)"
  let ?f = "\<lambda>z. h z / (z-w)"
  have fint: "set_integrable (lborel :: complex measure) ?S ?f"
    by (rule green_cauchy_density_integrable_cbox[OF hc])
  have Eeq: "?E = (\<lambda>(x,y). Complex x y)"
    by (rule ext) (auto simp: green_complex_of_pair_def)
  have Emeas: "?E \<in> measurable (lborel :: (real \<times> real) measure)
      (borel :: complex measure)"
    using green_complex_pair_measurable Eeq by simp
  have distr: "distr (lborel :: (real \<times> real) measure) borel ?E =
    (lborel :: complex measure)"
    using lborel_distr_complex_pair Eeq by simp
  have pull: "?E p \<in> ?S \<longleftrightarrow> p \<in> {a..b} \<times> {c..d}" for p
    by (simp add: green_complex_of_pair_rectangle)
  have "integrable (lborel :: (real \<times> real) measure)
    (\<lambda>p. indicator ?S (?E p) *\<^sub>R ?f (?E p))"
    by (rule integrable_distr[OF Emeas])
      (use fint distr in \<open>simp add: set_integrable_def\<close>)
  then show ?thesis
    by (simp add: set_integrable_def indicator_def pull)
qed

lemma green_wirtinger_dbar_continuous_on:
  fixes u :: "complex \<Rightarrow> complex"
  assumes C1: "Ck_on 1 u V"
  shows "continuous_on V (green_wirtinger_dbar u)"
proof -
  have dc: "continuous_on V
    (\<lambda>z. frechet_derivative u (at z) v)" for v
    using C1 by (simp add: Ck_on_Suc_iff Ck_on_0_iff)
  show ?thesis unfolding green_wirtinger_dbar_def
    by (intro continuous_intros dc) simp_all
qed

lemma green_cauchy_area_density_integrable:
  fixes u :: "complex \<Rightarrow> complex"
  assumes C1: "Ck_on 1 u V"
    and rect: "cbox (Complex a c) (Complex b d) \<subseteq> V"
  shows "set_integrable lborel ({a..b} \<times> {c..d})
    (\<lambda>p. green_wirtinger_dbar u (green_complex_of_pair p) /
      (green_complex_of_pair p - w))"
proof -
  have hc: "continuous_on (cbox (Complex a c) (Complex b d))
    (green_wirtinger_dbar u)"
    by (rule continuous_on_subset
      [OF green_wirtinger_dbar_continuous_on[OF C1] rect])
  show ?thesis by (rule green_cauchy_pair_integrable_cbox[OF hc])
qed

lemma green_shrinking_square_integral:
  fixes f :: "real \<times> real \<Rightarrow> complex"
  assumes fint: "integrable (lborel :: (real \<times> real) measure) f"
  shows "((\<lambda>e. LINT p:{x-e..x+e} \<times> {y-e..y+e}|lborel. f p)
    \<longlongrightarrow> 0) (at_right 0)"
proof -
  let ?S = "\<lambda>e. {x-e..x+e} \<times> {y-e..y+e}"
  let ?F = "\<lambda>t p. indicator (?S (inverse t)) p *\<^sub>R f p"
  have fmeas: "f \<in> borel_measurable lborel"
    by (rule borel_measurable_integrable[OF fint])
  have smeas: "?F t \<in> borel_measurable lborel" for t
  proof -
    have "?S (inverse t) \<in> sets (lborel :: (real \<times> real) measure)"
      by (simp add: borel_closed closed_Times)
    then show ?thesis using fmeas by measurable
  qed
  have normint: "integrable lborel (\<lambda>p. norm (f p))"
    by (rule integrable_norm[OF fint])
  have inv0: "((\<lambda>t::real. inverse t) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_inverse_0_at_top) (rule filterlim_ident)
  have ae: "AE p in (lborel :: (real \<times> real) measure).
      ((\<lambda>t. ?F t p) \<longlongrightarrow> 0) at_top"
  proof -
    have "AE p in (lborel :: (real \<times> real) measure).
      p \<noteq> (x,y)" by (rule AE_lborel_singleton)
    then show ?thesis
    proof eventually_elim
    fix p :: "real \<times> real"
    assume p: "p \<noteq> (x,y)"
    then consider "fst p \<noteq> x" | "snd p \<noteq> y"
      by (cases p) auto
    then show "((\<lambda>t. ?F t p) \<longlongrightarrow> 0) at_top"
    proof cases
      case 1
      have delta: "0 < abs (fst p - x)" using 1 by simp
      have ev: "eventually (\<lambda>t. inverse t < abs (fst p - x)) at_top"
        by (rule order_tendstoD(2)[OF inv0 delta])
      have ev0: "eventually (\<lambda>t. p \<notin> ?S (inverse t)) at_top"
        using ev by eventually_elim (auto simp: abs_le_iff)
      show ?thesis
      proof (rule tendsto_eventually)
        show "eventually (\<lambda>t. ?F t p = 0) at_top"
          using ev0 by eventually_elim (simp add: indicator_def)
      qed
    next
      case 2
      have delta: "0 < abs (snd p - y)" using 2 by simp
      have ev: "eventually (\<lambda>t. inverse t < abs (snd p - y)) at_top"
        by (rule order_tendstoD(2)[OF inv0 delta])
      have ev0: "eventually (\<lambda>t. p \<notin> ?S (inverse t)) at_top"
        using ev by eventually_elim (auto simp: abs_le_iff)
      show ?thesis
      proof (rule tendsto_eventually)
        show "eventually (\<lambda>t. ?F t p = 0) at_top"
          using ev0 by eventually_elim (simp add: indicator_def)
      qed
    qed
    qed
  qed
  have bound: "\<forall>\<^sub>F t in at_top.
    AE p in lborel. norm (?F t p) \<le> norm (f p)"
    by (intro always_eventually AE_I2) (simp add: indicator_def)
  have lim': "((\<lambda>t. integral\<^sup>L lborel (?F t)) \<longlongrightarrow>
    (integral\<^sup>L (lborel :: (real \<times> real) measure) (\<lambda>p. (0::complex)))) at_top"
    by (rule integral_dominated_convergence_at_top
      [where s="?F" and w="\<lambda>p. norm (f p)"
        and f="\<lambda>p. (0::complex)" and M="lborel"])
      (use fmeas smeas normint ae bound in auto)
  have lim: "((\<lambda>t. integral\<^sup>L lborel (?F t)) \<longlongrightarrow> 0) at_top"
    using lim' by simp
  show ?thesis
    using lim by (simp add: at_right_to_top
      tendsto_compose_filtermap[symmetric] set_lebesgue_integral_def comp_def)

qed

lemma green_shrinking_square_set_integral:
  fixes f :: "real \<times> real \<Rightarrow> complex"
  assumes ax: "a < x" and xb: "x < b"
    and cy: "c < y" and yd: "y < d"
    and fint: "set_integrable lborel ({a..b} \<times> {c..d}) f"
  shows "((\<lambda>e. LINT p:{x-e..x+e} \<times> {y-e..y+e}|lborel. f p)
    \<longlongrightarrow> 0) (at_right 0)"
proof -
  let ?S = "\<lambda>e. {x-e..x+e} \<times> {y-e..y+e}"
  let ?T = "{a..b} \<times> {c..d}"
  let ?g = "\<lambda>p. indicator ?T p *\<^sub>R f p"
  have gint: "integrable lborel ?g"
    using fint by (simp add: set_integrable_def)
  have lim: "((\<lambda>e. LINT p:?S e|lborel. ?g p)
    \<longlongrightarrow> 0) (at_right 0)"
    by (rule green_shrinking_square_integral[OF gint])
  let ?delta = "min (x-a) (min (b-x) (min (y-c) (d-y)))"
  have delta: "0 < ?delta" using ax xb cy yd by simp
  have ev: "eventually (\<lambda>e::real. 0 < e \<and> e < ?delta) (at_right 0)"
    using delta unfolding eventually_at_right_field
    by (intro exI[where x="min (x-a) (min (b-x) (min (y-c) (d-y)))"]) auto
  have eq: "(LINT p:?S e|lborel. f p) =
    (LINT p:?S e|lborel. ?g p)" if e: "0 < e" "e < ?delta" for e
  proof (rule set_lebesgue_integral_cong)
    show "?S e \<in> sets (lborel :: (real \<times> real) measure)"
      by (simp add: borel_closed closed_Times)
    show "\<forall>p. p \<in> ?S e \<longrightarrow> f p = ?g p"
      using e by (auto simp: indicator_def)
  qed
  have ev_eq: "eventually (\<lambda>e. (LINT p:?S e|lborel. f p) =
    (LINT p:?S e|lborel. ?g p)) (at_right 0)"
    using ev by eventually_elim (auto intro: eq)
  show ?thesis using lim ev_eq by (simp add: tendsto_cong)
qed

theorem green_cauchy_pompeiu_rectangle_interior:
  fixes u :: "complex \<Rightarrow> complex"
  assumes ab: "a < b" and cd: "c < d"
    and C1: "Ck_on 1 u V"
    and rect: "cbox (Complex a c) (Complex b d) \<subseteq> V"
    and inside: "w \<in> box (Complex a c) (Complex b d)"
  shows "contour_integral (rectpath (Complex a c) (Complex b d))
      (\<lambda>z. u z / (z-w)) =
    2 * pi * \<i> * u w + 2 * \<i> *
      (LINT p:{a..b} \<times> {c..d}|lborel.
        green_wirtinger_dbar u (green_complex_of_pair p) /
          (green_complex_of_pair p - w))"
proof -
  let ?x = "Re w"
  let ?y = "Im w"
  let ?f = "\<lambda>z. u z / (z-w)"
  let ?F = "\<lambda>p. green_wirtinger_dbar u (green_complex_of_pair p) /
    (green_complex_of_pair p-w)"
  let ?G = "\<lambda>e. green_cauchy_square_path w e"
  let ?T = "\<lambda>e. {?x-e..?x+e} \<times> {?y-e..?y+e}"
  have ax: "a < ?x" and xb: "?x < b"
    and cy: "c < ?y" and yd: "?y < d"
    using inside by (auto simp: in_box_complex_iff)
  have wV: "w \<in> V" using inside rect box_subset_cbox by blast
  have fint: "set_integrable lborel ({a..b} \<times> {c..d}) ?F"
    by (rule green_cauchy_area_density_integrable[OF C1 rect])
  have innerlim: "((\<lambda>e. contour_integral (?G e) ?f)
    \<longlongrightarrow> 2 * pi * \<i> * u w) (at_right 0)"
    by (rule green_cauchy_square_contour_limit[OF C1 wV])
  have arealim: "((\<lambda>e. LINT p:?T e|lborel. ?F p)
    \<longlongrightarrow> 0) (at_right 0)"
    by (rule green_shrinking_square_set_integral
      [OF ax xb cy yd fint])
  let ?delta = "min (?x-a) (min (b-?x) (min (?y-c) (d-?y)))"
  have delta: "0 < ?delta" using ax xb cy yd by simp
  have ident: "contour_integral
      (rectpath (Complex a c) (Complex b d)) ?f =
    contour_integral (?G e) ?f +
    2 * \<i> * ((LINT p:{a..b} \<times> {c..d}|lborel. ?F p) -
      (LINT p:?T e|lborel. ?F p))"
    if e: "0 < e" "e < ?delta" for e
  proof -
    have ap: "a < ?x-e" and pq: "?x-e < ?x+e"
      and qb: "?x+e < b" and cr: "c < ?y-e"
      and rs: "?y-e < ?y+e" and sd: "?y+e < d"
      using e by auto
    have win: "w \<in> box (Complex (?x-e) (?y-e))
      (Complex (?x+e) (?y+e))"
      using e by (simp add: in_box_complex_iff)
    show ?thesis
      using green_cauchy_punctured_rectangle
        [OF ap pq qb cr rs sd C1 rect win fint]
      by (simp add: green_cauchy_square_path_def)
  qed
  have ev: "eventually (\<lambda>e::real. 0 < e \<and> e < ?delta) (at_right 0)"
    using delta unfolding eventually_at_right_field
    by (intro exI[where x="min (Re w-a) (min (b-Re w)
      (min (Im w-c) (d-Im w)))"]) auto
  have ev_ident: "eventually (\<lambda>e.
    contour_integral (rectpath (Complex a c) (Complex b d)) ?f =
    contour_integral (?G e) ?f +
    2 * \<i> * ((LINT p:{a..b} \<times> {c..d}|lborel. ?F p) -
      (LINT p:?T e|lborel. ?F p))) (at_right 0)"
    using ev by eventually_elim (auto intro: ident)
  have diff_lim: "((\<lambda>e.
    (LINT p:{a..b} \<times> {c..d}|lborel. ?F p) -
      (LINT p:?T e|lborel. ?F p)) \<longlongrightarrow>
    (LINT p:{a..b} \<times> {c..d}|lborel. ?F p) - 0) (at_right 0)"
    by (rule tendsto_diff[OF tendsto_const arealim])
  have area_lim: "((\<lambda>e. 2 * \<i> *
    ((LINT p:{a..b} \<times> {c..d}|lborel. ?F p) -
      (LINT p:?T e|lborel. ?F p))) \<longlongrightarrow>
    2 * \<i> * (LINT p:{a..b} \<times> {c..d}|lborel. ?F p))
    (at_right 0)"
    using tendsto_mult[OF tendsto_const diff_lim] by simp
  have rhslim: "((\<lambda>e. contour_integral (?G e) ?f +
    2 * \<i> * ((LINT p:{a..b} \<times> {c..d}|lborel. ?F p) -
      (LINT p:?T e|lborel. ?F p))) \<longlongrightarrow>
    2 * pi * \<i> * u w + 2 * \<i> *
      (LINT p:{a..b} \<times> {c..d}|lborel. ?F p)) (at_right 0)"
    by (rule tendsto_add[OF innerlim area_lim])
  have ev_rev: "eventually (\<lambda>e.
    contour_integral (?G e) ?f +
      2 * \<i> * ((LINT p:{a..b} \<times> {c..d}|lborel. ?F p) -
        (LINT p:?T e|lborel. ?F p)) =
    contour_integral (rectpath (Complex a c) (Complex b d)) ?f)
    (at_right 0)"
    using ev_ident by (rule eventually_mono) auto
  have constlim: "((\<lambda>e. contour_integral (?G e) ?f +
      2 * \<i> * ((LINT p:{a..b} \<times> {c..d}|lborel. ?F p) -
        (LINT p:?T e|lborel. ?F p))) \<longlongrightarrow>
      contour_integral (rectpath (Complex a c) (Complex b d)) ?f)
      (at_right 0)"
    by (rule tendsto_eventually[OF ev_rev])
  have nontriv: "(at_right (0::real)) \<noteq> bot"
    using trivial_limit_at_right_real
    by (simp add: trivial_limit_def)
  show ?thesis
    by (rule tendsto_unique[OF nontriv constlim rhslim])
qed
end
