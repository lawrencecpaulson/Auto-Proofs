theory Green_Boundary_Walks
  imports Green_Edge_Flow
begin

datatype green_oriented_atom =
    Green_Horizontal real real real bool
  | Green_Vertical real real real bool

fun green_atom_start :: "green_oriented_atom \<Rightarrow> complex" where
  "green_atom_start (Green_Horizontal u v c forward) =
    (if forward then Complex u c else Complex v c)"
| "green_atom_start (Green_Vertical u v a forward) =
    (if forward then Complex a u else Complex a v)"

fun green_atom_end :: "green_oriented_atom \<Rightarrow> complex" where
  "green_atom_end (Green_Horizontal u v c forward) =
    (if forward then Complex v c else Complex u c)"
| "green_atom_end (Green_Vertical u v a forward) =
    (if forward then Complex a v else Complex a u)"

definition green_horizontal_directed_atoms where
  "green_horizontal_directed_atoms R c =
    map (\<lambda>(u,v). Green_Horizontal u v c
      (green_horizontal_atom_coefficient R c u v = 1))
      (green_exposed_horizontal_atoms R c)"

definition green_vertical_directed_atoms where
  "green_vertical_directed_atoms R a =
    map (\<lambda>(u,v). Green_Vertical u v a
      (green_vertical_atom_coefficient R a u v = 1))
      (green_exposed_vertical_atoms R a)"

definition green_directed_boundary where
  "green_directed_boundary R =
    concat (map (green_horizontal_directed_atoms R)
      (sorted_list_of_set (green_y_cuts R))) @
    concat (map (green_vertical_directed_atoms R)
      (sorted_list_of_set (green_x_cuts R)))"

definition green_directed_flux where
  "green_directed_flux z e =
    green_vertex_indicator z (green_atom_start e) -
    green_vertex_indicator z (green_atom_end e)"

lemma green_directed_horizontal_flux:
  assumes div: "green_rectangular_division R"
    and atom: "(u,v) \<in> set (green_exposed_horizontal_atoms R c)"
  shows "green_directed_flux z (Green_Horizontal u v c
      (green_horizontal_atom_coefficient R c u v = 1)) =
    green_horizontal_atom_coefficient R c u v *
      green_horizontal_flux z c u v"
proof -
  have member: "(u,v) \<in> set (green_x_atoms R)"
    and nz: "green_horizontal_atom_coefficient R c u v \<noteq> 0"
    using atom by (auto simp: green_exposed_horizontal_atoms_def)
  have range: "green_horizontal_atom_coefficient R c u v \<in> {-1,0,1}"
    by (rule green_horizontal_atom_orientation(1)[OF div member])
  show ?thesis using range nz
    by (auto simp: green_directed_flux_def green_horizontal_flux_def
      green_vertex_indicator_def)
qed

lemma green_directed_vertical_flux:
  assumes div: "green_rectangular_division R"
    and atom: "(u,v) \<in> set (green_exposed_vertical_atoms R a)"
  shows "green_directed_flux z (Green_Vertical u v a
      (green_vertical_atom_coefficient R a u v = 1)) =
    green_vertical_atom_coefficient R a u v *
      green_vertical_flux z a u v"
proof -
  have member: "(u,v) \<in> set (green_y_atoms R)"
    and nz: "green_vertical_atom_coefficient R a u v \<noteq> 0"
    using atom by (auto simp: green_exposed_vertical_atoms_def)
  have range: "green_vertical_atom_coefficient R a u v \<in> {-1,0,1}"
    by (rule green_vertical_atom_orientation(1)[OF div member])
  show ?thesis using range nz
    by (auto simp: green_directed_flux_def green_vertical_flux_def
      green_vertex_indicator_def)
qed

lemma green_directed_horizontal_flux_sum:
  assumes "green_rectangular_division R"
  shows "(\<Sum>e\<leftarrow>green_horizontal_directed_atoms R c.
      green_directed_flux z e) =
    (\<Sum>(u,v)\<leftarrow>green_exposed_horizontal_atoms R c.
      green_horizontal_atom_coefficient R c u v *
        green_horizontal_flux z c u v)"
  unfolding green_horizontal_directed_atoms_def
  by (intro arg_cong[where f=sum_list] map_cong)
    (use green_directed_horizontal_flux[OF assms] in
      \<open>auto split: prod.splits\<close>)

lemma green_directed_vertical_flux_sum:
  assumes "green_rectangular_division R"
  shows "(\<Sum>e\<leftarrow>green_vertical_directed_atoms R a.
      green_directed_flux z e) =
    (\<Sum>(u,v)\<leftarrow>green_exposed_vertical_atoms R a.
      green_vertical_atom_coefficient R a u v *
        green_vertical_flux z a u v)"
  unfolding green_vertical_directed_atoms_def
  by (intro arg_cong[where f=sum_list] map_cong)
    (use green_directed_vertical_flux[OF assms] in
      \<open>auto split: prod.splits\<close>)

lemma green_cuts_sum_list:
  assumes "finite C"
  shows "(\<Sum>c\<leftarrow>sorted_list_of_set C. f c) = (\<Sum>c\<in>C. f c)"
  using assms by (simp add: sum_list_distinct_conv_sum_set)

lemma green_sum_list_subtract_int:
  fixes f g :: "'a \<Rightarrow> int"
  shows "(\<Sum>x\<leftarrow>xs. f x - g x) =
    (\<Sum>x\<leftarrow>xs. f x) - (\<Sum>x\<leftarrow>xs. g x)"
  by (induction xs) simp_all

lemma green_sum_list_concat_map:
  shows "(\<Sum>e\<leftarrow>concat (map g xs). f e) =
    (\<Sum>x\<leftarrow>xs. \<Sum>e\<leftarrow>g x. f e)"
  by (induction xs) simp_all

lemma green_sum_list_concat:
  "(\<Sum>e\<leftarrow>concat xs. f e) =
    (\<Sum>ys\<leftarrow>xs. \<Sum>e\<leftarrow>ys. f e)"
  using green_sum_list_concat_map[where g=id and xs=xs and f=f]
  by simp

lemma green_directed_boundary_flux:
  assumes div: "green_rectangular_division R"
  shows "(\<Sum>e\<leftarrow>green_directed_boundary R. green_directed_flux z e) =
    green_subdivided_flux R z"
proof -
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have finx: "finite (green_x_cuts R)" and finy: "finite (green_y_cuts R)"
    by (rule green_cuts_finite[OF fin])+
  have H: "(\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_exposed_horizontal_atoms R c.
      green_horizontal_atom_coefficient R c u v *
        green_horizontal_flux z c u v) =
    (\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_x_atoms R.
      green_horizontal_atom_coefficient R c u v *
        green_horizontal_flux z c u v)"
    unfolding green_exposed_horizontal_atoms_def
    by (rule sum.cong[OF refl])
      (rule sum_list_map_filter; auto split: prod.splits)
  have V: "(\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_exposed_vertical_atoms R a.
      green_vertical_atom_coefficient R a u v *
        green_vertical_flux z a u v) =
    (\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_y_atoms R.
      green_vertical_atom_coefficient R a u v *
        green_vertical_flux z a u v)"
    unfolding green_exposed_vertical_atoms_def
    by (rule sum.cong[OF refl])
      (rule sum_list_map_filter; auto split: prod.splits)
  have HL: "(\<Sum>e\<leftarrow>concat (map (green_horizontal_directed_atoms R)
      (sorted_list_of_set (green_y_cuts R))). green_directed_flux z e) =
    (\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_exposed_horizontal_atoms R c.
      green_horizontal_atom_coefficient R c u v *
        green_horizontal_flux z c u v)"
    by (simp add: green_sum_list_concat_map green_cuts_sum_list[OF finy]
      green_directed_horizontal_flux_sum[OF div])
  have VL: "(\<Sum>e\<leftarrow>concat (map (green_vertical_directed_atoms R)
      (sorted_list_of_set (green_x_cuts R))). green_directed_flux z e) =
    (\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_exposed_vertical_atoms R a.
      green_vertical_atom_coefficient R a u v *
        green_vertical_flux z a u v)"
    by (simp add: green_sum_list_concat_map green_cuts_sum_list[OF finx]
      green_directed_vertical_flux_sum[OF div])
  show ?thesis
    unfolding green_directed_boundary_def green_subdivided_flux_def
    using H V HL VL by simp
qed

theorem green_directed_boundary_balanced:
  assumes "green_rectangular_division R"
  shows "(\<Sum>e\<leftarrow>green_directed_boundary R.
      green_vertex_indicator z (green_atom_start e)) =
    (\<Sum>e\<leftarrow>green_directed_boundary R.
      green_vertex_indicator z (green_atom_end e))"
proof -
  have "(\<Sum>e\<leftarrow>green_directed_boundary R.
      green_vertex_indicator z (green_atom_start e)) -
    (\<Sum>e\<leftarrow>green_directed_boundary R.
      green_vertex_indicator z (green_atom_end e)) = 0"
    using green_directed_boundary_flux[OF assms, of z]
      green_subdivided_flux_zero[OF assms, of z]
    by (simp add: green_directed_flux_def green_sum_list_subtract_int)
  then show ?thesis by simp
qed

fun green_walk_from :: "complex \<Rightarrow> green_oriented_atom list \<Rightarrow> complex \<Rightarrow> bool" where
  "green_walk_from u [] v = (u = v)"
| "green_walk_from u (e # es) v =
    (u = green_atom_start e \<and> green_walk_from (green_atom_end e) es v)"

definition green_closed_walk :: "green_oriented_atom list \<Rightarrow> bool" where
  "green_closed_walk es \<longleftrightarrow>
    es \<noteq> [] \<and> (\<exists>u. green_walk_from u es u)"

lemma green_walk_from_append:
  "green_walk_from u (xs @ ys) v \<longleftrightarrow>
    (\<exists>w. green_walk_from u xs w \<and> green_walk_from w ys v)"
  by (induction xs arbitrary: u) auto

lemma green_walk_flux:
  assumes "green_walk_from u es v"
  shows "(\<Sum>e\<in>#mset es. green_directed_flux z e) =
    green_vertex_indicator z u - green_vertex_indicator z v"
  using assms
  by (induction es arbitrary: u) (auto simp: green_directed_flux_def algebra_simps)

definition green_balanced_edges :: "green_oriented_atom multiset \<Rightarrow> bool" where
  "green_balanced_edges E \<longleftrightarrow>
    (\<forall>z. (\<Sum>e\<in>#E. green_directed_flux z e) = 0)"

lemma green_closed_walk_balanced:
  assumes "green_closed_walk es"
  shows "green_balanced_edges (mset es)"
  using assms green_walk_flux
  by (auto simp: green_closed_walk_def green_balanced_edges_def)

lemma green_sum_mset_list:
  "(\<Sum>e\<in>#mset xs. f e) = (\<Sum>e\<leftarrow>xs. f e)"
  by (induction xs) simp_all

lemma green_directed_boundary_balanced_mset:
  assumes "green_rectangular_division R"
  shows "green_balanced_edges (mset (green_directed_boundary R))"
proof (unfold green_balanced_edges_def, intro allI)
  fix z
  show "(\<Sum>e\<in>#mset (green_directed_boundary R).
      green_directed_flux z e) = 0"
    using green_directed_boundary_flux[OF assms, of z]
      green_subdivided_flux_zero[OF assms, of z]
    by (simp add: green_sum_mset_list)
qed

lemma green_positive_flux_has_outgoing:
  assumes "0 < (\<Sum>e\<in>#E. green_directed_flux z e)"
  shows "\<exists>e\<in>#E. green_atom_start e = z"
proof (rule ccontr)
  assume no: "\<not> (\<exists>e\<in>#E. green_atom_start e = z)"
  have out: "(\<Sum>e\<in>#E. green_vertex_indicator z (green_atom_start e)) = 0"
    using no by (induction E) (auto simp: green_vertex_indicator_def)
  have incoming: "0 \<le> (\<Sum>e\<in>#E.
      green_vertex_indicator z (green_atom_end e))"
    by (induction E) (auto simp: green_vertex_indicator_def)
  have "(\<Sum>e\<in>#E. green_directed_flux z e) =
    - (\<Sum>e\<in>#E. green_vertex_indicator z (green_atom_end e))"
    using out by (simp add: green_directed_flux_def sum_mset_subtractf)
  then show False using assms incoming by linarith
qed

lemma green_extend_to_closed:
  assumes bal: "green_balanced_edges E"
    and sub: "mset w \<subseteq># E"
    and walk: "green_walk_from u w v"
    and nonempty: "w \<noteq> []"
  shows "\<exists>t. green_walk_from u (w @ t) u \<and> mset (w @ t) \<subseteq># E"
  using sub walk nonempty
proof (induction "size E - length w" arbitrary: w v rule: less_induct)
  case less
  show ?case
  proof (cases "u = v")
    case True
    then show ?thesis using less.prems(1,2) by (intro exI[where x="[]"]) simp
  next
    case False
    obtain M where EM: "E = mset w + M"
      using less.prems(1) by (auto simp: mset_subset_eq_exists_conv)
    have wf: "(\<Sum>e\<in>#mset w. green_directed_flux v e) = -1"
      using green_walk_flux[OF less.prems(2), of v] False
      by (simp add: green_vertex_indicator_def)
    have Ef: "(\<Sum>e\<in>#E. green_directed_flux v e) = 0"
      using bal by (simp add: green_balanced_edges_def)
    have mf: "(\<Sum>e\<in>#M. green_directed_flux v e) = 1"
      using Ef EM wf by simp
    obtain e where e: "e \<in># M" "green_atom_start e = v"
      using green_positive_flux_has_outgoing[of v M] mf by auto
    have Msplit: "M = {#e#} + (M - {#e#})"
      using e(1) by simp
    have sub': "mset (w @ [e]) \<subseteq># E"
      using EM Msplit by (auto simp: mset_subset_eq_exists_conv ac_simps)
    have walk': "green_walk_from u (w @ [e]) (green_atom_end e)"
      using less.prems(2) e(2)
      by (simp add: green_walk_from_append)
    have posM: "0 < size M"
    proof (rule ccontr)
      assume "\<not> 0 < size M"
      then have "M = {#}" by simp
      with e(1) show False by simp
    qed
    have sizeE: "size E = length w + size M" using EM by simp
    have len: "length w < size E"
      using sizeE posM by linarith
    have smaller: "size E - length (w @ [e]) < size E - length w"
      using len by simp
    obtain t where t: "green_walk_from u ((w @ [e]) @ t) u"
      "mset ((w @ [e]) @ t) \<subseteq># E"
      using less.hyps[OF smaller sub' walk'] by auto
    show ?thesis
      using t by (intro exI[where x="e # t"]) simp
  qed
qed

theorem green_balanced_edges_decompose:
  assumes "green_balanced_edges E"
  shows "\<exists>ws. (\<forall>w\<in>set ws. green_closed_walk w) \<and>
    mset (concat ws) = E"
  using assms
proof (induction "size E" arbitrary: E rule: less_induct)
  case less
  show ?case
  proof (cases "E = {#}")
    case True
    then show ?thesis by (intro exI[where x="[]"]) simp
  next
    case False
    then obtain e where e: "e \<in># E" by auto
    have sub: "mset [e] \<subseteq># E" using e by simp
    obtain t where t: "green_walk_from (green_atom_start e)
        ([e] @ t) (green_atom_start e)"
      "mset ([e] @ t) \<subseteq># E"
      by (rule exE[OF green_extend_to_closed[
        OF less.prems sub, of "green_atom_start e" "green_atom_end e"]])
        (use e in auto)
    let ?w = "[e] @ t"
    have closed: "green_closed_walk ?w"
      using t(1) by (simp add: green_closed_walk_def)
    obtain M where EM: "E = mset ?w + M"
      using t(2) by (auto simp: mset_subset_eq_exists_conv)
    have Mbal: "green_balanced_edges M"
    proof (unfold green_balanced_edges_def, intro allI)
      fix z
      have Ef: "(\<Sum>a\<in>#E. green_directed_flux z a) = 0"
        using less.prems by (simp add: green_balanced_edges_def)
      have wf: "(\<Sum>a\<in>#mset ?w. green_directed_flux z a) = 0"
        using green_closed_walk_balanced[OF closed]
        by (simp add: green_balanced_edges_def)
      show "(\<Sum>a\<in>#M. green_directed_flux z a) = 0"
        using Ef wf EM by simp
    qed
    have small: "size M < size E" using EM by simp
    obtain ws where ws: "(\<forall>w\<in>set ws. green_closed_walk w)"
      "mset (concat ws) = M"
      using less.hyps[OF small Mbal] by blast
    show ?thesis
      using closed ws EM
      by (intro exI[where x="?w # ws"]) simp
  qed
qed

theorem green_boundary_closed_walks:
  assumes div: "green_rectangular_division R"
  shows "\<exists>ws. (\<forall>w\<in>set ws. green_closed_walk w) \<and>
    mset (concat ws) = mset (green_directed_boundary R)"
  by (rule green_balanced_edges_decompose[
    OF green_directed_boundary_balanced_mset[OF div]])

end
