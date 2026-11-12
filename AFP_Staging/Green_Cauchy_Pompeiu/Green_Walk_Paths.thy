theory Green_Walk_Paths
  imports Green_Boundary_Contour
begin

fun green_walk_path :: "green_oriented_atom list \<Rightarrow> real \<Rightarrow> complex" where
  "green_walk_path [] = linepath 0 0"
| "green_walk_path [e] = linepath (green_atom_start e) (green_atom_end e)"
| "green_walk_path (e # f # es) =
    linepath (green_atom_start e) (green_atom_end e) +++
      green_walk_path (f # es)"

lemmas green_walk_path_induct [case_names empty singleton step] =
  green_walk_path.induct

lemma green_walk_path_ends:
  assumes walk: "green_walk_from u es v" and nonempty: "es \<noteq> []"
  shows "pathstart (green_walk_path es) = u \<and>
    pathfinish (green_walk_path es) = v \<and>
    valid_path (green_walk_path es)"
proof -
  have key: "green_walk_from u es v \<Longrightarrow> es \<noteq> [] \<Longrightarrow>
    pathstart (green_walk_path es) = u \<and>
    pathfinish (green_walk_path es) = v \<and>
    valid_path (green_walk_path es)" for u es v
  proof (induction es arbitrary: u v rule: green_walk_path_induct)
    case empty
    then show ?case by simp
  next
    case (singleton e)
    then show ?case by simp
  next
    case (step e f es)
    have u: "u = green_atom_start e"
      and tail: "green_walk_from (green_atom_end e) (f # es) v"
      using step.prems(1) by simp_all
    have rest: "pathstart (green_walk_path (f # es)) = green_atom_end e"
      "pathfinish (green_walk_path (f # es)) = v"
      "valid_path (green_walk_path (f # es))"
      using step.IH[OF tail] by simp_all
    show ?case using u rest
      by (simp add: valid_path_join)
  qed
  show ?thesis by (rule key[OF walk nonempty])
qed

lemma green_closed_walk_path:
  assumes "green_closed_walk w"
  shows "valid_path (green_walk_path w)"
    "pathfinish (green_walk_path w) = pathstart (green_walk_path w)"
proof -
  obtain u where nonempty: "w \<noteq> []" and walk: "green_walk_from u w u"
    using assms by (auto simp: green_closed_walk_def)
  have ends: "pathstart (green_walk_path w) = u \<and>
      pathfinish (green_walk_path w) = u \<and>
      valid_path (green_walk_path w)"
    by (rule green_walk_path_ends[OF walk nonempty])
  show "valid_path (green_walk_path w)"
    using ends by simp
  show "pathfinish (green_walk_path w) = pathstart (green_walk_path w)"
    using ends by simp
qed

lemma green_horizontal_oriented_integrable:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
    and atom: "(u,v) \<in> set (green_exposed_horizontal_atoms R c)"
  shows "(green_contour_coefficient P Q) contour_integrable_on
    linepath (green_atom_start (Green_Horizontal u v c forward))
      (green_atom_end (Green_Horizontal u v c forward))"
proof -
  have cont: "continuous_on (closed_segment (Complex u c) (Complex v c))
      (green_contour_coefficient P Q)"
    by (rule green_horizontal_exposed_continuous(3)[OF div C1 atom])
  have reverse: "continuous_on (closed_segment (Complex v c) (Complex u c))
      (green_contour_coefficient P Q)"
    using cont by (simp add: closed_segment_commute)
  show ?thesis
    by (cases forward)
      (auto intro: contour_integrable_continuous_linepath[OF cont]
        contour_integrable_continuous_linepath[OF reverse])
qed

lemma green_vertical_oriented_integrable:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
    and atom: "(u,v) \<in> set (green_exposed_vertical_atoms R a)"
  shows "(green_contour_coefficient P Q) contour_integrable_on
    linepath (green_atom_start (Green_Vertical u v a forward))
      (green_atom_end (Green_Vertical u v a forward))"
proof -
  have cont: "continuous_on (closed_segment (Complex a u) (Complex a v))
      (green_contour_coefficient P Q)"
    by (rule green_vertical_exposed_continuous(3)[OF div C1 atom])
  have reverse: "continuous_on (closed_segment (Complex a v) (Complex a u))
      (green_contour_coefficient P Q)"
    using cont by (simp add: closed_segment_commute)
  show ?thesis
    by (cases forward)
      (auto intro: contour_integrable_continuous_linepath[OF cont]
        contour_integrable_continuous_linepath[OF reverse])
qed

lemma green_boundary_atom_integrable:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
    and atom: "e \<in> set (green_directed_boundary R)"
  shows "(green_contour_coefficient P Q) contour_integrable_on
    linepath (green_atom_start e) (green_atom_end e)"
  using atom
  unfolding green_directed_boundary_def green_horizontal_directed_atoms_def
    green_vertical_directed_atoms_def
  by (auto intro: green_horizontal_oriented_integrable[OF div C1]
      green_vertical_oriented_integrable[OF div C1]
    split: prod.splits)

lemma green_walk_path_contour_integral:
  fixes f :: "complex \<Rightarrow> complex"
  assumes walk: "green_walk_from u es v" and nonempty: "es \<noteq> []"
    and edges: "\<And>e. e \<in> set es \<Longrightarrow>
      f contour_integrable_on linepath (green_atom_start e) (green_atom_end e)"
  shows "f contour_integrable_on green_walk_path es \<and>
    contour_integral (green_walk_path es) f =
      (\<Sum>e\<leftarrow>es. contour_integral
        (linepath (green_atom_start e) (green_atom_end e)) f)"
proof -
  have key: "green_walk_from u es v \<Longrightarrow> es \<noteq> [] \<Longrightarrow>
      (\<forall>e\<in>set es. f contour_integrable_on
        linepath (green_atom_start e) (green_atom_end e)) \<Longrightarrow>
      f contour_integrable_on green_walk_path es \<and>
      contour_integral (green_walk_path es) f =
        (\<Sum>e\<leftarrow>es. contour_integral
          (linepath (green_atom_start e) (green_atom_end e)) f)"
    for u es v
  proof (induction es arbitrary: u v rule: green_walk_path_induct)
    case empty
    then show ?case by simp
  next
    case (singleton e)
    then show ?case by simp
  next
    case (step e g es)
    have tail: "green_walk_from (green_atom_end e) (g # es) v"
      using step.prems(1) by simp
    have tail_edges: "\<forall>a\<in>set (g # es). f contour_integrable_on
        linepath (green_atom_start a) (green_atom_end a)"
      using step.prems(3) by simp
    have rest: "f contour_integrable_on green_walk_path (g # es)"
      "contour_integral (green_walk_path (g # es)) f =
        (\<Sum>a\<leftarrow>g # es. contour_integral
          (linepath (green_atom_start a) (green_atom_end a)) f)"
      using step.IH[OF tail _ tail_edges] by simp_all
    have valid: "valid_path (green_walk_path (g # es))"
      using green_walk_path_ends[OF tail] by simp
    have first: "f contour_integrable_on
        linepath (green_atom_start e) (green_atom_end e)"
      using step.prems(3) by simp
    show ?case
      using rest valid first
      by (simp add: contour_integrable_join contour_integral_join)
  qed
  show ?thesis by (rule key[OF walk nonempty]) (use edges in auto)
qed

theorem Green_rectangular_union_polygonal_contours:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
  shows "\<exists>ws.
    (\<forall>w\<in>set ws. valid_path (green_walk_path w) \<and>
      pathfinish (green_walk_path w) = pathstart (green_walk_path w)) \<and>
    mset (concat ws) = mset (green_directed_boundary R) \<and>
    (LINT p:green_rectangular_region R|lborel.
      frechet_derivative Q (at p) (1,0) -
      frechet_derivative P (at p) (0,1)) =
    Re (\<Sum>w\<leftarrow>ws. contour_integral (green_walk_path w)
      (green_contour_coefficient P Q))"
proof -
  obtain ws where closed: "\<forall>w\<in>set ws. green_closed_walk w"
    and edges: "mset (concat ws) = mset (green_directed_boundary R)"
    and area: "(LINT p:green_rectangular_region R|lborel.
        frechet_derivative Q (at p) (1,0) -
        frechet_derivative P (at p) (0,1)) =
      Re (\<Sum>w\<leftarrow>ws. green_walk_contour_integral P Q w)"
    using Green_rectangular_union_closed_walks[OF div C1] by blast
  have seteq: "set (concat ws) = set (green_directed_boundary R)"
    using edges by (metis set_mset_mset)
  have path: "valid_path (green_walk_path w) \<and>
      pathfinish (green_walk_path w) = pathstart (green_walk_path w)"
    if "w \<in> set ws" for w
    using green_closed_walk_path[OF closed[rule_format, OF that]] by simp
  have integral: "contour_integral (green_walk_path w)
      (green_contour_coefficient P Q) =
    green_walk_contour_integral P Q w"
    if win: "w \<in> set ws" for w
  proof -
    obtain u where nonempty: "w \<noteq> []" and walk: "green_walk_from u w u"
      using closed win by (auto simp: green_closed_walk_def)
    have subset: "set w \<subseteq> set (green_directed_boundary R)"
      using win seteq by auto
    have each: "(green_contour_coefficient P Q) contour_integrable_on
        linepath (green_atom_start e) (green_atom_end e)"
      if "e \<in> set w" for e
      by (rule green_boundary_atom_integrable[OF div C1])
        (use subset that in auto)
    have result: "contour_integral (green_walk_path w)
        (green_contour_coefficient P Q) =
      (\<Sum>e\<leftarrow>w. contour_integral
        (linepath (green_atom_start e) (green_atom_end e))
          (green_contour_coefficient P Q))"
      using green_walk_path_contour_integral[OF walk nonempty each] by simp
    show ?thesis using result
      by (simp add: green_walk_contour_integral_def
        green_atom_contour_integral_def)
  qed
  have sums: "(\<Sum>w\<leftarrow>ws. contour_integral (green_walk_path w)
      (green_contour_coefficient P Q)) =
    (\<Sum>w\<leftarrow>ws. green_walk_contour_integral P Q w)"
    by (intro arg_cong[where f=sum_list] map_cong)
      (use integral in auto)
  have conclusion: "(LINT p:green_rectangular_region R|lborel.
      frechet_derivative Q (at p) (1,0) -
      frechet_derivative P (at p) (0,1)) =
    Re (\<Sum>w\<leftarrow>ws. contour_integral (green_walk_path w)
      (green_contour_coefficient P Q))"
    using area sums by simp
  show ?thesis
    by (intro exI[where x=ws])
      (use path edges conclusion in auto)
qed

end
