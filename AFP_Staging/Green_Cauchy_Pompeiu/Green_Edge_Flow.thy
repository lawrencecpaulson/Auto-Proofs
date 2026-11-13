theory Green_Edge_Flow
  imports Green_Edge_Contour
begin

text \<open>The endpoint contribution of a subdivided interval telescopes.
  This is the one-dimensional reason each rectangle boundary has no
  endpoint.\<close>
lemma green_selected_atoms_telescope:
  fixes f :: "real \<Rightarrow> int"
  assumes "sorted xs" "distinct xs" "a \<in> set xs" "b \<in> set xs" "a \<le> b"
  shows "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs xs.
      if a \<le> u \<and> v \<le> b then f u - f v else 0) = f a - f b"
  using assms
proof (induction xs arbitrary: a b rule: green_adjacent_pairs_induct)
  case empty
  then show ?case by simp
next
  case (singleton x)
  then show ?case by simp
next
  case (step x y xs)
  have xy: "x < y" using step.prems(1,2) by auto
  show ?case
  proof (cases "a = x")
    case True
    show ?thesis
    proof (cases "b = x")
      case True
      have no: "\<not> (a \<le> u \<and> v \<le> b)"
        if "(u,v) \<in> set (green_adjacent_pairs (y # xs))" for u v
        using green_adjacent_pairs_endpoints(2)[OF that]
          step.prems(1) xy \<open>a = x\<close> True by auto
      have zero: "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs (y # xs).
          if a \<le> u \<and> v \<le> b then f u - f v else 0) = 0"
        by (rule sum_list_neutral) (use no in \<open>auto split: prod.splits\<close>)
      show ?thesis using True \<open>a = x\<close> zero xy by simp
    next
      case False
      have yin: "y \<le> b" using step.prems(1,4,5) False \<open>a = x\<close> by auto
      have bin: "b \<in> set (y # xs)" using step.prems(4) False by simp
      have tail: "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs (y # xs).
          if y \<le> u \<and> v \<le> b then f u - f v else 0) = f y - f b"
        using step.IH[of y b] step.prems(1,2) bin yin by simp
      have uge: "y \<le> u"
        if "(u,v) \<in> set (green_adjacent_pairs (y # xs))" for u v
        using green_adjacent_pairs_endpoints(1)[OF that] step.prems(1) by auto
      have equiv: "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs (y # xs).
          if a \<le> u \<and> v \<le> b then f u - f v else 0) =
        (\<Sum>(u,v)\<leftarrow>green_adjacent_pairs (y # xs).
          if y \<le> u \<and> v \<le> b then f u - f v else 0)"
        by (intro arg_cong[where f=sum_list] map_cong)
          (use uge \<open>a = x\<close> xy in \<open>auto split: prod.splits\<close>)
      show ?thesis using tail equiv xy yin \<open>a = x\<close> by simp
    qed
  next
    case False
    have ain: "a \<in> set (y # xs)" using step.prems(3) False by simp
    have xle: "x \<le> a" using step.prems(1) ain by auto
    have xa: "x < a" using xle False by linarith
    have bin: "b \<in> set (y # xs)" using step.prems(4,5) xa by auto
    have tail: "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs (y # xs).
        if a \<le> u \<and> v \<le> b then f u - f v else 0) = f a - f b"
      using step.IH[of a b] step.prems ain bin by simp
    show ?thesis using tail xa by simp
  qed
qed

lemma green_cut_atoms_telescope:
  fixes f :: "real \<Rightarrow> int"
  assumes "finite C" "a \<in> C" "b \<in> C" "a \<le> b"
  shows "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs (sorted_list_of_set C).
      if a \<le> u \<and> v \<le> b then f u - f v else 0) = f a - f b"
  by (rule green_selected_atoms_telescope)
    (use assms in auto)

lemma green_axis_telescope:
  fixes f :: "real \<Rightarrow> real \<Rightarrow> int"
  assumes "finite L" "c \<in> L" "finite C" "a \<in> C" "b \<in> C" "a \<le> b"
  shows "(\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>green_adjacent_pairs (sorted_list_of_set C).
      if l = c \<and> a \<le> u \<and> v \<le> b then f l u - f l v else 0) =
    f c a - f c b"
proof -
  let ?atoms = "green_adjacent_pairs (sorted_list_of_set C)"
  have inner: "(\<Sum>(u,v)\<leftarrow>?atoms.
      if l = c \<and> a \<le> u \<and> v \<le> b then f l u - f l v else 0) =
    (if l = c then
      (\<Sum>(u,v)\<leftarrow>?atoms. if a \<le> u \<and> v \<le> b then f c u - f c v else 0)
      else 0)" for l
  proof (cases "l = c")
    case True
    have rewrite: "(\<Sum>(u,v)\<leftarrow>?atoms.
        if l = c \<and> a \<le> u \<and> v \<le> b then f l u - f l v else 0) =
      (\<Sum>(u,v)\<leftarrow>?atoms.
        if a \<le> u \<and> v \<le> b then f c u - f c v else 0)"
      by (intro arg_cong[where f=sum_list] map_cong)
        (use True in \<open>auto split: prod.splits\<close>)
    show ?thesis using True rewrite by simp
  next
    case False
    have "(\<Sum>(u,v)\<leftarrow>?atoms. (0::int)) = 0"
      by (rule sum_list_neutral) auto
    then show ?thesis using False by simp
  qed
  have "(\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>?atoms.
      if l = c \<and> a \<le> u \<and> v \<le> b then f l u - f l v else 0) =
    (\<Sum>l\<in>L. if l = c then
      (\<Sum>(u,v)\<leftarrow>?atoms. if a \<le> u \<and> v \<le> b then f c u - f c v else 0)
      else 0)"
    by (rule sum.cong[OF refl]) (rule inner)
  also have "\<dots> =
    (\<Sum>(u,v)\<leftarrow>?atoms. if a \<le> u \<and> v \<le> b then f c u - f c v else 0)"
    using assms(1,2) by simp
  also have "\<dots> = f c a - f c b"
    by (rule green_cut_atoms_telescope[OF assms(3-6)])
  finally show ?thesis .
qed

lemma green_axis_signed_telescope:
  fixes f :: "real \<Rightarrow> real \<Rightarrow> int"
  assumes "finite L" "c \<in> L" "d \<in> L" "finite C" "a \<in> C" "b \<in> C" "a \<le> b"
  shows "(\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>green_adjacent_pairs (sorted_list_of_set C).
      ((if l = c \<and> a \<le> u \<and> v \<le> b then 1 else 0) -
       (if l = d \<and> a \<le> u \<and> v \<le> b then 1 else 0)) *
      (f l u - f l v)) =
    (f c a - f c b) - (f d a - f d b)"
proof -
  let ?atoms = "green_adjacent_pairs (sorted_list_of_set C)"
  have inner: "(\<Sum>(u,v)\<leftarrow>?atoms.
      ((if l = c \<and> a \<le> u \<and> v \<le> b then 1 else 0) -
       (if l = d \<and> a \<le> u \<and> v \<le> b then 1 else 0)) *
      (f l u - f l v)) =
    (\<Sum>(u,v)\<leftarrow>?atoms.
      if l = c \<and> a \<le> u \<and> v \<le> b then f l u - f l v else 0) -
    (\<Sum>(u,v)\<leftarrow>?atoms.
      if l = d \<and> a \<le> u \<and> v \<le> b then f l u - f l v else 0)"
    for l
  proof -
    have point: "((if l = c \<and> a \<le> u \<and> v \<le> b then 1 else 0) -
        (if l = d \<and> a \<le> u \<and> v \<le> b then 1 else 0)) *
        (f l u - f l v) =
      (if l = c \<and> a \<le> u \<and> v \<le> b then f l u - f l v else 0) -
      (if l = d \<and> a \<le> u \<and> v \<le> b then f l u - f l v else 0)"
      for u v
      by (simp add: green_signed_indicator)
    have rewrite: "(\<Sum>(u,v)\<leftarrow>?atoms.
        ((if l = c \<and> a \<le> u \<and> v \<le> b then 1 else 0) -
         (if l = d \<and> a \<le> u \<and> v \<le> b then 1 else 0)) *
        (f l u - f l v)) =
      (\<Sum>(u,v)\<leftarrow>?atoms.
        (if l = c \<and> a \<le> u \<and> v \<le> b then f l u - f l v else 0) -
        (if l = d \<and> a \<le> u \<and> v \<le> b then f l u - f l v else 0))"
      by (intro arg_cong[where f=sum_list] map_cong)
        (use point in \<open>auto split: prod.splits\<close>)
    show ?thesis using rewrite
      by (simp add: green_sum_list_pair_subtract)
  qed
  have "(\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>?atoms.
      ((if l = c \<and> a \<le> u \<and> v \<le> b then 1 else 0) -
       (if l = d \<and> a \<le> u \<and> v \<le> b then 1 else 0)) *
      (f l u - f l v)) =
    (\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>?atoms.
      if l = c \<and> a \<le> u \<and> v \<le> b then f l u - f l v else 0) -
    (\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>?atoms.
      if l = d \<and> a \<le> u \<and> v \<le> b then f l u - f l v else 0)"
    by (simp add: inner sum_subtractf)
  also have "\<dots> = (f c a - f c b) - (f d a - f d b)"
    using green_axis_telescope[OF assms(1,2,4-7)]
      green_axis_telescope[OF assms(1,3,4-7)] by simp
  finally show ?thesis .
qed

definition green_vertex_indicator :: "complex \<Rightarrow> complex \<Rightarrow> int" where
  "green_vertex_indicator z w = (if z = w then 1 else 0)"

definition green_horizontal_flux :: "complex \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int" where
  "green_horizontal_flux z c u v =
    green_vertex_indicator z (Complex u c) -
    green_vertex_indicator z (Complex v c)"

definition green_vertical_flux :: "complex \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int" where
  "green_vertical_flux z a u v =
    green_vertex_indicator z (Complex a u) -
    green_vertex_indicator z (Complex a v)"

lemma green_rectangle_subdivided_flux_zero:
  assumes div: "green_rectangular_division R" and r: "r \<in> R"
  shows "(\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_x_atoms R.
      green_horizontal_cell_coefficient r c u v *
        green_horizontal_flux z c u v) +
    (\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_y_atoms R.
      green_vertical_cell_coefficient r a u v *
        green_vertical_flux z a u v) = 0"
proof -
  let ?a = "Re (fst r)" and ?b = "Re (snd r)"
  let ?c = "Im (fst r)" and ?d = "Im (snd r)"
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have order: "?a \<le> ?b" "?c \<le> ?d"
    using div r by (auto simp: green_rectangular_division_def)
  have cuts: "finite (green_x_cuts R)" "finite (green_y_cuts R)"
    by (rule green_cuts_finite[OF fin])+
  have endpoints: "?a \<in> green_x_cuts R" "?b \<in> green_x_cuts R"
    "?c \<in> green_y_cuts R" "?d \<in> green_y_cuts R"
    using r by (auto simp: green_x_cuts_def green_y_cuts_def)
  have H: "(\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_x_atoms R.
      green_horizontal_cell_coefficient r c u v *
        green_horizontal_flux z c u v) =
    (green_vertex_indicator z (Complex ?a ?c) -
      green_vertex_indicator z (Complex ?b ?c)) -
    (green_vertex_indicator z (Complex ?a ?d) -
      green_vertex_indicator z (Complex ?b ?d))"
    using green_axis_signed_telescope[
      of "green_y_cuts R" ?c ?d "green_x_cuts R" ?a ?b
        "\<lambda>c x. green_vertex_indicator z (Complex x c)",
      OF cuts(2) endpoints(3) endpoints(4) cuts(1)
        endpoints(1) endpoints(2) order(1)]
    by (simp add: green_x_atoms_def green_horizontal_cell_coefficient_def
      green_horizontal_flux_def)
  have V: "(\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_y_atoms R.
      green_vertical_cell_coefficient r a u v *
        green_vertical_flux z a u v) =
    (green_vertex_indicator z (Complex ?b ?c) -
      green_vertex_indicator z (Complex ?b ?d)) -
    (green_vertex_indicator z (Complex ?a ?c) -
      green_vertex_indicator z (Complex ?a ?d))"
    using green_axis_signed_telescope[
      of "green_x_cuts R" ?b ?a "green_y_cuts R" ?c ?d
        "\<lambda>a y. green_vertex_indicator z (Complex a y)",
      OF cuts(1) endpoints(2) endpoints(1) cuts(2)
        endpoints(3) endpoints(4) order(2)]
    by (simp add: green_y_atoms_def green_vertical_cell_coefficient_def
      green_vertical_flux_def)
  show ?thesis using H V by simp
qed

definition green_subdivided_flux :: "green_rectangle set \<Rightarrow> complex \<Rightarrow> int" where
  "green_subdivided_flux R z =
    (\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_x_atoms R.
      green_horizontal_atom_coefficient R c u v *
        green_horizontal_flux z c u v) +
    (\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_y_atoms R.
      green_vertical_atom_coefficient R a u v *
        green_vertical_flux z a u v)"

lemma green_atom_coefficient_flux_sum:
  fixes k :: "'r \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> int"
    and f :: "'a \<Rightarrow> 'b \<Rightarrow> int"
  shows "(\<Sum>(u,v)\<leftarrow>ts. (\<Sum>r\<in>R. k r u v) * f u v) =
    (\<Sum>(u,v)\<leftarrow>ts. \<Sum>r\<in>R. k r u v * f u v)"
  by (intro arg_cong[where f=sum_list] map_cong)
    (auto simp: sum_distrib_right split: prod.splits)

theorem green_subdivided_flux_zero:
  assumes div: "green_rectangular_division R"
  shows "green_subdivided_flux R z = 0"
proof -
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have H: "(\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_x_atoms R.
      green_horizontal_atom_coefficient R c u v *
        green_horizontal_flux z c u v) =
    (\<Sum>r\<in>R. \<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_x_atoms R.
      green_horizontal_cell_coefficient r c u v *
        green_horizontal_flux z c u v)"
    unfolding green_horizontal_atom_coefficient_def
    by (simp add: green_atom_coefficient_flux_sum
      green_sum_line_atoms_swap_pair)
  have V: "(\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_y_atoms R.
      green_vertical_atom_coefficient R a u v *
        green_vertical_flux z a u v) =
    (\<Sum>r\<in>R. \<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_y_atoms R.
      green_vertical_cell_coefficient r a u v *
        green_vertical_flux z a u v)"
    unfolding green_vertical_atom_coefficient_def
    by (simp add: green_atom_coefficient_flux_sum
      green_sum_line_atoms_swap_pair)
  have "green_subdivided_flux R z =
    (\<Sum>r\<in>R.
      (\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_x_atoms R.
        green_horizontal_cell_coefficient r c u v *
          green_horizontal_flux z c u v) +
      (\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_y_atoms R.
        green_vertical_cell_coefficient r a u v *
          green_vertical_flux z a u v))"
    using H V by (simp add: green_subdivided_flux_def sum.distrib)
  also have "\<dots> = 0"
    by (rule sum.neutral) (use green_rectangle_subdivided_flux_zero[OF div] in auto)
  finally show ?thesis .
qed

end
