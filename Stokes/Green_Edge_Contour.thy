theory Green_Edge_Contour
  imports Green_Edge_Orientation
begin

lemma green_horizontal_linepath_integral:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes uv: "u \<le> v"
    and P: "continuous_on {u..v} (\<lambda>x. P (x,c))"
    and Q: "continuous_on {u..v} (\<lambda>x. Q (x,c))"
  shows "Re (contour_integral (linepath (Complex u c) (Complex v c))
      (green_contour_coefficient P Q)) =
    green_edge_integral P Q (Horizontal u v c)"
proof -
  have F: "continuous_on {u..v}
      (\<lambda>x. green_contour_coefficient P Q (Complex x c))"
    unfolding green_contour_coefficient_def
    using P Q by (auto intro!: continuous_intros)
  show ?thesis
    using P F
    by (simp add: contour_integral_horizontal[OF uv]
      green_contour_coefficient_def Re_integral_complex_Icc
      integral_lborel_Icc[OF borel_integrable_atLeastAtMost'])
qed

lemma green_vertical_linepath_integral:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes uv: "u \<le> v"
    and P: "continuous_on {u..v} (\<lambda>y. P (a,y))"
    and Q: "continuous_on {u..v} (\<lambda>y. Q (a,y))"
  shows "Re (contour_integral (linepath (Complex a u) (Complex a v))
      (green_contour_coefficient P Q)) =
    green_edge_integral P Q (Vertical u v a)"
proof (cases "u = v")
  case True
  then show ?thesis
    by (simp add: lborel_integral_singleton_zero)
next
  case False
  with uv have lt: "u < v" by simp
  have F: "continuous_on {u..v}
      (\<lambda>y. green_contour_coefficient P Q (Complex a y))"
    unfolding green_contour_coefficient_def
    using P Q by (auto intro!: continuous_intros)
  show ?thesis
    using P Q F lt
    by (simp add: contour_integral_linepath_same_Re
      green_contour_coefficient_def Im_integral_complex_Icc
      integral_lborel_Icc[OF borel_integrable_atLeastAtMost'])
qed

lemma green_horizontal_exposed_support:
  assumes div: "green_rectangular_division R"
    and atom: "(u,v) \<in> set (green_exposed_horizontal_atoms R c)"
  obtains r where "r \<in> R"
    "Re (fst r) \<le> u" "v \<le> Re (snd r)"
    "Im (fst r) \<le> c" "c \<le> Im (snd r)"
proof -
  have member: "(u,v) \<in> set (green_x_atoms R)"
    and nz: "green_horizontal_atom_coefficient R c u v \<noteq> 0"
    using atom by (auto simp: green_exposed_horizontal_atoms_def)
  have sides: "green_horizontal_above R c u v \<noteq> {} \<or>
    green_horizontal_below R c u v \<noteq> {}"
    using green_horizontal_atom_orientation(4)[OF div member] nz by auto
  then obtain r where "r \<in> R"
    "Re (fst r) \<le> u" "v \<le> Re (snd r)"
    "Im (fst r) \<le> c" "c \<le> Im (snd r)"
    by (auto simp: green_horizontal_above_def green_horizontal_below_def)
  then show thesis by (rule that)
qed

lemma green_vertical_exposed_support:
  assumes div: "green_rectangular_division R"
    and atom: "(u,v) \<in> set (green_exposed_vertical_atoms R a)"
  obtains r where "r \<in> R"
    "Im (fst r) \<le> u" "v \<le> Im (snd r)"
    "Re (fst r) \<le> a" "a \<le> Re (snd r)"
proof -
  have member: "(u,v) \<in> set (green_y_atoms R)"
    and nz: "green_vertical_atom_coefficient R a u v \<noteq> 0"
    using atom by (auto simp: green_exposed_vertical_atoms_def)
  have sides: "green_vertical_left R a u v \<noteq> {} \<or>
    green_vertical_right R a u v \<noteq> {}"
    using green_vertical_atom_orientation(4)[OF div member] nz by auto
  then obtain r where "r \<in> R"
    "Im (fst r) \<le> u" "v \<le> Im (snd r)"
    "Re (fst r) \<le> a" "a \<le> Re (snd r)"
    by (auto simp: green_vertical_left_def green_vertical_right_def)
  then show thesis by (rule that)
qed

lemma green_rectangle_C1_segment_continuous:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes cell: "green_rectangle_C1 P Q a b c d"
    and p: "p \<in> cbox (Complex a c) (Complex b d)"
    and q: "q \<in> cbox (Complex a c) (Complex b d)"
  shows "continuous_on (closed_segment p q) (green_contour_coefficient P Q)"
proof -
  have ab: "a \<le> b" and cd: "c \<le> d"
    using p by (auto simp: in_cbox_complex_iff)
  have PC: "continuous_on ({a..b} \<times> {c..d}) P"
    using green_rectangle_C1_continuous_on(1)[OF cell] .
  have QC: "continuous_on ({a..b} \<times> {c..d}) Q"
    using green_rectangle_C1_continuous_on(2)[OF cell] .
  have cont: "continuous_on (cbox (Complex a c) (Complex b d))
      (green_contour_coefficient P Q)"
    by (rule green_contour_continuous[OF ab cd PC QC])
  have subset: "closed_segment p q \<subseteq> cbox (Complex a c) (Complex b d)"
    by (rule closed_segment_subset[OF p q convex_box(1)])
  show ?thesis by (rule continuous_on_subset[OF cont subset])
qed

lemma green_horizontal_exposed_continuous:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
    and atom: "(u,v) \<in> set (green_exposed_horizontal_atoms R c)"
  shows "continuous_on {u..v} (\<lambda>x. P (x,c))"
    "continuous_on {u..v} (\<lambda>x. Q (x,c))"
    "continuous_on (closed_segment (Complex u c) (Complex v c))
      (green_contour_coefficient P Q)"
proof -
  obtain r where r: "r \<in> R"
    and bounds: "Re (fst r) \<le> u" "v \<le> Re (snd r)"
      "Im (fst r) \<le> c" "c \<le> Im (snd r)"
    by (rule green_horizontal_exposed_support[OF div atom])
  let ?a = "Re (fst r)" and ?b = "Re (snd r)"
  let ?c = "Im (fst r)" and ?d = "Im (snd r)"
  have cell: "green_rectangle_C1 P Q ?a ?b ?c ?d"
    by (rule green_rectangular_C1_cell[OF C1 r])
  have PC: "continuous_on ({?a..?b} \<times> {?c..?d}) P"
    using green_rectangle_C1_continuous_on(1)[OF cell] .
  have QC: "continuous_on ({?a..?b} \<times> {?c..?d}) Q"
    using green_rectangle_C1_continuous_on(2)[OF cell] .
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have member: "(u,v) \<in> set (green_x_atoms R)"
    using atom by (auto simp: green_exposed_horizontal_atoms_def)
  have uv: "u \<le> v"
    using green_atomic_segments(1)[OF fin member] by simp
  have sub: "(\<lambda>x. (x,c)) ` {u..v} \<subseteq> {?a..?b} \<times> {?c..?d}"
    using bounds by auto
  have coord: "continuous_on {u..v} (\<lambda>x. (x,c))"
    by (intro continuous_intros)
  show "continuous_on {u..v} (\<lambda>x. P (x,c))"
    by (rule continuous_on_compose2[OF PC coord sub])
  show "continuous_on {u..v} (\<lambda>x. Q (x,c))"
    by (rule continuous_on_compose2[OF QC coord sub])
  have p: "Complex u c \<in> cbox (Complex ?a ?c) (Complex ?b ?d)"
    and q: "Complex v c \<in> cbox (Complex ?a ?c) (Complex ?b ?d)"
    using bounds uv by (auto simp: in_cbox_complex_iff)
  show "continuous_on (closed_segment (Complex u c) (Complex v c))
      (green_contour_coefficient P Q)"
    by (rule green_rectangle_C1_segment_continuous[OF cell p q])
qed

lemma green_vertical_exposed_continuous:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
    and atom: "(u,v) \<in> set (green_exposed_vertical_atoms R a)"
  shows "continuous_on {u..v} (\<lambda>y. P (a,y))"
    "continuous_on {u..v} (\<lambda>y. Q (a,y))"
    "continuous_on (closed_segment (Complex a u) (Complex a v))
      (green_contour_coefficient P Q)"
proof -
  obtain r where r: "r \<in> R"
    and bounds: "Im (fst r) \<le> u" "v \<le> Im (snd r)"
      "Re (fst r) \<le> a" "a \<le> Re (snd r)"
    by (rule green_vertical_exposed_support[OF div atom])
  let ?a = "Re (fst r)" and ?b = "Re (snd r)"
  let ?c = "Im (fst r)" and ?d = "Im (snd r)"
  have cell: "green_rectangle_C1 P Q ?a ?b ?c ?d"
    by (rule green_rectangular_C1_cell[OF C1 r])
  have PC: "continuous_on ({?a..?b} \<times> {?c..?d}) P"
    using green_rectangle_C1_continuous_on(1)[OF cell] .
  have QC: "continuous_on ({?a..?b} \<times> {?c..?d}) Q"
    using green_rectangle_C1_continuous_on(2)[OF cell] .
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have member: "(u,v) \<in> set (green_y_atoms R)"
    using atom by (auto simp: green_exposed_vertical_atoms_def)
  have uv: "u \<le> v"
    using green_atomic_segments(2)[OF fin member] by simp
  have sub: "(\<lambda>y. (a,y)) ` {u..v} \<subseteq> {?a..?b} \<times> {?c..?d}"
    using bounds by auto
  have coord: "continuous_on {u..v} (\<lambda>y. (a,y))"
    by (intro continuous_intros)
  show "continuous_on {u..v} (\<lambda>y. P (a,y))"
    by (rule continuous_on_compose2[OF PC coord sub])
  show "continuous_on {u..v} (\<lambda>y. Q (a,y))"
    by (rule continuous_on_compose2[OF QC coord sub])
  have p: "Complex a u \<in> cbox (Complex ?a ?c) (Complex ?b ?d)"
    and q: "Complex a v \<in> cbox (Complex ?a ?c) (Complex ?b ?d)"
    using bounds uv by (auto simp: in_cbox_complex_iff)
  show "continuous_on (closed_segment (Complex a u) (Complex a v))
      (green_contour_coefficient P Q)"
    by (rule green_rectangle_C1_segment_continuous[OF cell p q])
qed

end
