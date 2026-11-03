theory Green_Boundary_Contour
  imports Green_Boundary_Walks
begin

fun green_oriented_atom_integral ::
    "(real \<times> real \<Rightarrow> real) \<Rightarrow> (real \<times> real \<Rightarrow> real) \<Rightarrow>
      green_oriented_atom \<Rightarrow> real" where
  "green_oriented_atom_integral P Q (Green_Horizontal u v c forward) =
    (if forward then green_edge_integral P Q (Horizontal u v c)
      else - green_edge_integral P Q (Horizontal u v c))"
| "green_oriented_atom_integral P Q (Green_Vertical u v a forward) =
    (if forward then green_edge_integral P Q (Vertical u v a)
      else - green_edge_integral P Q (Vertical u v a))"

definition green_atom_contour_integral ::
    "(real \<times> real \<Rightarrow> real) \<Rightarrow> (real \<times> real \<Rightarrow> real) \<Rightarrow>
      green_oriented_atom \<Rightarrow> complex" where
  "green_atom_contour_integral P Q e =
    contour_integral (linepath (green_atom_start e) (green_atom_end e))
      (green_contour_coefficient P Q)"

lemma green_horizontal_oriented_contour:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
    and atom: "(u,v) \<in> set (green_exposed_horizontal_atoms R c)"
  shows "Re (green_atom_contour_integral P Q
      (Green_Horizontal u v c forward)) =
    green_oriented_atom_integral P Q (Green_Horizontal u v c forward)"
proof -
  have cont: "continuous_on {u..v} (\<lambda>x. P (x,c))"
    "continuous_on {u..v} (\<lambda>x. Q (x,c))"
    "continuous_on (closed_segment (Complex u c) (Complex v c))
      (green_contour_coefficient P Q)"
    by (rule green_horizontal_exposed_continuous[OF div C1 atom])+
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have member: "(u,v) \<in> set (green_x_atoms R)"
    using atom by (auto simp: green_exposed_horizontal_atoms_def)
  have uv: "u \<le> v" using green_atomic_segments(1)[OF fin member] by simp
  have pos: "Re (green_atom_contour_integral P Q
      (Green_Horizontal u v c True)) =
    green_edge_integral P Q (Horizontal u v c)"
    using green_horizontal_linepath_integral[OF uv cont(1,2)]
    by (simp add: green_atom_contour_integral_def)
  have neg: "Re (green_atom_contour_integral P Q
      (Green_Horizontal u v c False)) =
    - green_edge_integral P Q (Horizontal u v c)"
    using contour_integral_reverse_linepath[OF cont(3)] pos
    by (simp add: green_atom_contour_integral_def)
  show ?thesis using pos neg by (cases forward) simp_all
qed

lemma green_vertical_oriented_contour:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
    and atom: "(u,v) \<in> set (green_exposed_vertical_atoms R a)"
  shows "Re (green_atom_contour_integral P Q
      (Green_Vertical u v a forward)) =
    green_oriented_atom_integral P Q (Green_Vertical u v a forward)"
proof -
  have cont: "continuous_on {u..v} (\<lambda>y. P (a,y))"
    "continuous_on {u..v} (\<lambda>y. Q (a,y))"
    "continuous_on (closed_segment (Complex a u) (Complex a v))
      (green_contour_coefficient P Q)"
    by (rule green_vertical_exposed_continuous[OF div C1 atom])+
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have member: "(u,v) \<in> set (green_y_atoms R)"
    using atom by (auto simp: green_exposed_vertical_atoms_def)
  have uv: "u \<le> v" using green_atomic_segments(2)[OF fin member] by simp
  have pos: "Re (green_atom_contour_integral P Q
      (Green_Vertical u v a True)) =
    green_edge_integral P Q (Vertical u v a)"
    using green_vertical_linepath_integral[OF uv cont(1,2)]
    by (simp add: green_atom_contour_integral_def)
  have neg: "Re (green_atom_contour_integral P Q
      (Green_Vertical u v a False)) =
    - green_edge_integral P Q (Vertical u v a)"
    using contour_integral_reverse_linepath[OF cont(3)] pos
    by (simp add: green_atom_contour_integral_def)
  show ?thesis using pos neg by (cases forward) simp_all
qed

lemma green_boundary_atom_contour:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
    and atom: "e \<in> set (green_directed_boundary R)"
  shows "Re (green_atom_contour_integral P Q e) =
    green_oriented_atom_integral P Q e"
  using atom
  unfolding green_directed_boundary_def green_horizontal_directed_atoms_def
    green_vertical_directed_atoms_def
  by (auto intro: green_horizontal_oriented_contour[OF div C1]
      green_vertical_oriented_contour[OF div C1]
    split: prod.splits)

lemma green_directed_boundary_sum:
  assumes "finite R"
  shows "(\<Sum>e\<leftarrow>green_directed_boundary R. f e) =
    (\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_exposed_horizontal_atoms R c.
      f (Green_Horizontal u v c
        (green_horizontal_atom_coefficient R c u v = 1))) +
    (\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_exposed_vertical_atoms R a.
      f (Green_Vertical u v a
        (green_vertical_atom_coefficient R a u v = 1)))"
proof -
  have cuts: "finite (green_x_cuts R)" "finite (green_y_cuts R)"
    by (rule green_cuts_finite[OF assms])+
  have H: "(\<Sum>e\<leftarrow>green_horizontal_directed_atoms R c. f e) =
    (\<Sum>(u,v)\<leftarrow>green_exposed_horizontal_atoms R c.
      f (Green_Horizontal u v c
        (green_horizontal_atom_coefficient R c u v = 1)))" for c
    unfolding green_horizontal_directed_atoms_def
    by (intro arg_cong[where f=sum_list] map_cong)
      (auto split: prod.splits)
  have V: "(\<Sum>e\<leftarrow>green_vertical_directed_atoms R a. f e) =
    (\<Sum>(u,v)\<leftarrow>green_exposed_vertical_atoms R a.
      f (Green_Vertical u v a
        (green_vertical_atom_coefficient R a u v = 1)))" for a
    unfolding green_vertical_directed_atoms_def
    by (intro arg_cong[where f=sum_list] map_cong)
      (auto split: prod.splits)
  show ?thesis
    unfolding green_directed_boundary_def
    by (simp add: green_sum_list_concat_map
      green_cuts_sum_list[OF cuts(1)] green_cuts_sum_list[OF cuts(2)]
      H V)
qed

lemma green_horizontal_oriented_integral:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and atom: "(u,v) \<in> set (green_exposed_horizontal_atoms R c)"
  shows "green_oriented_atom_integral P Q
      (Green_Horizontal u v c
        (green_horizontal_atom_coefficient R c u v = 1)) =
    of_int (green_horizontal_atom_coefficient R c u v) *
      green_edge_integral P Q (Horizontal u v c)"
proof -
  have member: "(u,v) \<in> set (green_x_atoms R)"
    and nz: "green_horizontal_atom_coefficient R c u v \<noteq> 0"
    using atom by (auto simp: green_exposed_horizontal_atoms_def)
  have range: "green_horizontal_atom_coefficient R c u v \<in> {-1,0,1}"
    by (rule green_horizontal_atom_orientation(1)[OF div member])
  show ?thesis using range nz by auto
qed

lemma green_vertical_oriented_integral:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and atom: "(u,v) \<in> set (green_exposed_vertical_atoms R a)"
  shows "green_oriented_atom_integral P Q
      (Green_Vertical u v a
        (green_vertical_atom_coefficient R a u v = 1)) =
    of_int (green_vertical_atom_coefficient R a u v) *
      green_edge_integral P Q (Vertical u v a)"
proof -
  have member: "(u,v) \<in> set (green_y_atoms R)"
    and nz: "green_vertical_atom_coefficient R a u v \<noteq> 0"
    using atom by (auto simp: green_exposed_vertical_atoms_def)
  have range: "green_vertical_atom_coefficient R a u v \<in> {-1,0,1}"
    by (rule green_vertical_atom_orientation(1)[OF div member])
  show ?thesis using range nz by auto
qed

lemma green_directed_boundary_integral_eq:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
  shows "(\<Sum>e\<leftarrow>green_directed_boundary R.
      green_oriented_atom_integral P Q e) =
    green_subdivided_boundary_integral P Q R"
proof -
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have H: "(\<Sum>(u,v)\<leftarrow>green_exposed_horizontal_atoms R c.
      green_oriented_atom_integral P Q
        (Green_Horizontal u v c
          (green_horizontal_atom_coefficient R c u v = 1))) =
    (\<Sum>(u,v)\<leftarrow>green_exposed_horizontal_atoms R c.
      of_int (green_horizontal_atom_coefficient R c u v) *
        green_edge_integral P Q (Horizontal u v c))" for c
  proof -
    have point: "green_oriented_atom_integral P Q
        (Green_Horizontal u v c
          (green_horizontal_atom_coefficient R c u v = 1)) =
      of_int (green_horizontal_atom_coefficient R c u v) *
        green_edge_integral P Q (Horizontal u v c)"
      if "(u,v) \<in> set (green_exposed_horizontal_atoms R c)" for u v
      by (rule green_horizontal_oriented_integral[OF div that])
    show ?thesis
    proof (intro arg_cong[where f=sum_list] map_cong)
      fix x
      assume x: "x \<in> set (green_exposed_horizontal_atoms R c)"
      obtain u v where pair: "x = (u,v)" by (cases x) auto
      have uv: "(u,v) \<in> set (green_exposed_horizontal_atoms R c)"
        using x pair by simp
      have fact: "green_oriented_atom_integral P Q
          (Green_Horizontal u v c
            (green_horizontal_atom_coefficient R c u v = 1)) =
        of_int (green_horizontal_atom_coefficient R c u v) *
          green_edge_integral P Q (Horizontal u v c)"
        by (rule point[OF uv])
      show "(case x of (u,v) \<Rightarrow> green_oriented_atom_integral P Q
          (Green_Horizontal u v c
            (green_horizontal_atom_coefficient R c u v = 1))) =
        (case x of (u,v) \<Rightarrow>
          of_int (green_horizontal_atom_coefficient R c u v) *
            green_edge_integral P Q (Horizontal u v c))"
        using fact by (simp add: pair)
    qed simp
  qed
  have V: "(\<Sum>(u,v)\<leftarrow>green_exposed_vertical_atoms R a.
      green_oriented_atom_integral P Q
        (Green_Vertical u v a
          (green_vertical_atom_coefficient R a u v = 1))) =
    (\<Sum>(u,v)\<leftarrow>green_exposed_vertical_atoms R a.
      of_int (green_vertical_atom_coefficient R a u v) *
        green_edge_integral P Q (Vertical u v a))" for a
  proof -
    have point: "green_oriented_atom_integral P Q
        (Green_Vertical u v a
          (green_vertical_atom_coefficient R a u v = 1)) =
      of_int (green_vertical_atom_coefficient R a u v) *
        green_edge_integral P Q (Vertical u v a)"
      if "(u,v) \<in> set (green_exposed_vertical_atoms R a)" for u v
      by (rule green_vertical_oriented_integral[OF div that])
    show ?thesis
    proof (intro arg_cong[where f=sum_list] map_cong)
      fix x
      assume x: "x \<in> set (green_exposed_vertical_atoms R a)"
      obtain u v where pair: "x = (u,v)" by (cases x) auto
      have uv: "(u,v) \<in> set (green_exposed_vertical_atoms R a)"
        using x pair by simp
      have fact: "green_oriented_atom_integral P Q
          (Green_Vertical u v a
            (green_vertical_atom_coefficient R a u v = 1)) =
        of_int (green_vertical_atom_coefficient R a u v) *
          green_edge_integral P Q (Vertical u v a)"
        by (rule point[OF uv])
      show "(case x of (u,v) \<Rightarrow> green_oriented_atom_integral P Q
          (Green_Vertical u v a
            (green_vertical_atom_coefficient R a u v = 1))) =
        (case x of (u,v) \<Rightarrow>
          of_int (green_vertical_atom_coefficient R a u v) *
            green_edge_integral P Q (Vertical u v a))"
        using fact by (simp add: pair)
    qed simp
  qed
  show ?thesis
    using green_directed_boundary_sum[OF fin, of
        "green_oriented_atom_integral P Q"] H V
      green_subdivided_boundary_exposed[of P Q R]
    by simp
qed

lemma green_Re_sum_list:
  fixes f :: "'a \<Rightarrow> complex"
  shows "Re (\<Sum>x\<leftarrow>xs. f x) = (\<Sum>x\<leftarrow>xs. Re (f x))"
  by (induction xs) simp_all

theorem Green_rectangular_union_boundary_contour:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
  shows "(LINT p:green_rectangular_region R|lborel.
      frechet_derivative Q (at p) (1,0) -
      frechet_derivative P (at p) (0,1)) =
    Re (\<Sum>e\<leftarrow>green_directed_boundary R.
      green_atom_contour_integral P Q e)"
proof -
  have point: "Re (green_atom_contour_integral P Q e) =
      green_oriented_atom_integral P Q e"
    if "e \<in> set (green_directed_boundary R)" for e
    by (rule green_boundary_atom_contour[OF div C1 that])
  have sum: "Re (\<Sum>e\<leftarrow>green_directed_boundary R.
      green_atom_contour_integral P Q e) =
    (\<Sum>e\<leftarrow>green_directed_boundary R.
      green_oriented_atom_integral P Q e)"
    by (simp add: green_Re_sum_list)
      (intro arg_cong[where f=sum_list] map_cong;
        use point in auto)
  show ?thesis
    using Green_rectangular_union_exposed[OF div C1] sum
      green_directed_boundary_integral_eq[OF div, of P Q]
      green_subdivided_boundary_exposed[of P Q R]
    by simp
qed

definition green_walk_contour_integral ::
    "(real \<times> real \<Rightarrow> real) \<Rightarrow> (real \<times> real \<Rightarrow> real) \<Rightarrow>
      green_oriented_atom list \<Rightarrow> complex" where
  "green_walk_contour_integral P Q w =
    (\<Sum>e\<leftarrow>w. green_atom_contour_integral P Q e)"

theorem Green_rectangular_union_closed_walks:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
  shows "\<exists>ws. (\<forall>w\<in>set ws. green_closed_walk w) \<and>
    mset (concat ws) = mset (green_directed_boundary R) \<and>
    (LINT p:green_rectangular_region R|lborel.
      frechet_derivative Q (at p) (1,0) -
      frechet_derivative P (at p) (0,1)) =
    Re (\<Sum>w\<leftarrow>ws. green_walk_contour_integral P Q w)"
proof -
  obtain ws where walks: "\<forall>w\<in>set ws. green_closed_walk w"
    and edges: "mset (concat ws) = mset (green_directed_boundary R)"
    using green_boundary_closed_walks[OF div] by blast
  have sum: "(\<Sum>w\<leftarrow>ws. green_walk_contour_integral P Q w) =
    (\<Sum>e\<leftarrow>green_directed_boundary R.
      green_atom_contour_integral P Q e)"
  proof -
    have "(\<Sum>w\<leftarrow>ws. green_walk_contour_integral P Q w) =
      (\<Sum>e\<leftarrow>concat ws. green_atom_contour_integral P Q e)"
      unfolding green_walk_contour_integral_def
      by (rule green_sum_list_concat[symmetric])
    also have "\<dots> =
      (\<Sum>e\<in>#mset (concat ws). green_atom_contour_integral P Q e)"
      by (rule green_sum_mset_list[symmetric])
    also have "\<dots> =
      (\<Sum>e\<in>#mset (green_directed_boundary R).
        green_atom_contour_integral P Q e)"
      using edges by simp
    also have "\<dots> =
      (\<Sum>e\<leftarrow>green_directed_boundary R.
        green_atom_contour_integral P Q e)"
      by (rule green_sum_mset_list)
    finally show ?thesis .
  qed
  have area: "(LINT p:green_rectangular_region R|lborel.
      frechet_derivative Q (at p) (1,0) -
      frechet_derivative P (at p) (0,1)) =
    Re (\<Sum>w\<leftarrow>ws. green_walk_contour_integral P Q w)"
    using Green_rectangular_union_boundary_contour[OF div C1] sum
    by simp
  show ?thesis
    by (intro exI[where x=ws]) (use walks edges area in simp)
qed

end
