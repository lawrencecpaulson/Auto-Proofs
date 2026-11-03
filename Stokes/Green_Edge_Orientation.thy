theory Green_Edge_Orientation
  imports Green_Edge_Subdivision
begin

text \<open>An elementary edge sees at most one rectangle on either side.
  Zero-area rectangles have no occupied side.\<close>

definition green_horizontal_below where
  "green_horizontal_below R c u v =
    {r \<in> R. Re (fst r) \<le> u \<and> v \<le> Re (snd r) \<and>
      Im (fst r) < c \<and> Im (snd r) = c}"

definition green_horizontal_above where
  "green_horizontal_above R c u v =
    {r \<in> R. Re (fst r) \<le> u \<and> v \<le> Re (snd r) \<and>
      Im (fst r) = c \<and> c < Im (snd r)}"

definition green_vertical_left where
  "green_vertical_left R a u v =
    {r \<in> R. Im (fst r) \<le> u \<and> v \<le> Im (snd r) \<and>
      Re (fst r) < a \<and> Re (snd r) = a}"

definition green_vertical_right where
  "green_vertical_right R a u v =
    {r \<in> R. Im (fst r) \<le> u \<and> v \<le> Im (snd r) \<and>
      Re (fst r) = a \<and> a < Re (snd r)}"

lemma green_rectangles_no_open_overlap:
  assumes div: "green_rectangular_division R"
    and r: "r \<in> R" and s: "s \<in> R"
    and x: "max (Re (fst r)) (Re (fst s)) <
      min (Re (snd r)) (Re (snd s))"
    and y: "max (Im (fst r)) (Im (fst s)) <
      min (Im (snd r)) (Im (snd s))"
  shows "r = s"
proof (rule ccontr)
  assume neq: "r \<noteq> s"
  let ?x = "(max (Re (fst r)) (Re (fst s)) +
    min (Re (snd r)) (Re (snd s))) / 2"
  let ?y = "(max (Im (fst r)) (Im (fst s)) +
    min (Im (snd r)) (Im (snd s))) / 2"
  have " (?x,?y) \<in> green_rectangle_open r \<inter> green_rectangle_open s"
    using x y by (auto simp: green_rectangle_open_def box_prod; linarith)
  moreover have "green_rectangle_open r \<inter> green_rectangle_open s = {}"
    using div r s neq by (auto simp: green_rectangular_division_def)
  ultimately show False by simp
qed

lemma green_horizontal_side_unique:
  assumes div: "green_rectangular_division R" and uv: "u < v"
  shows "\<And>r s. r \<in> green_horizontal_below R c u v \<Longrightarrow>
      s \<in> green_horizontal_below R c u v \<Longrightarrow> r = s"
    "\<And>r s. r \<in> green_horizontal_above R c u v \<Longrightarrow>
      s \<in> green_horizontal_above R c u v \<Longrightarrow> r = s"
proof -
  fix r s
  assume r: "r \<in> green_horizontal_below R c u v"
    and s: "s \<in> green_horizontal_below R c u v"
  have xy: "max (Re (fst r)) (Re (fst s)) <
      min (Re (snd r)) (Re (snd s))"
    using r s uv by (auto simp: green_horizontal_below_def; linarith)
  have yy: "max (Im (fst r)) (Im (fst s)) <
      min (Im (snd r)) (Im (snd s))"
    using r s by (auto simp: green_horizontal_below_def; linarith)
  show "r = s"
    by (rule green_rectangles_no_open_overlap[OF div _ _ xy yy])
      (use r s in \<open>auto simp: green_horizontal_below_def\<close>)
next
  fix r s
  assume r: "r \<in> green_horizontal_above R c u v"
    and s: "s \<in> green_horizontal_above R c u v"
  have xy: "max (Re (fst r)) (Re (fst s)) <
      min (Re (snd r)) (Re (snd s))"
    using r s uv by (auto simp: green_horizontal_above_def; linarith)
  have yy: "max (Im (fst r)) (Im (fst s)) <
      min (Im (snd r)) (Im (snd s))"
    using r s by (auto simp: green_horizontal_above_def; linarith)
  show "r = s"
    by (rule green_rectangles_no_open_overlap[OF div _ _ xy yy])
      (use r s in \<open>auto simp: green_horizontal_above_def\<close>)
qed

lemma green_vertical_side_unique:
  assumes div: "green_rectangular_division R" and uv: "u < v"
  shows "\<And>r s. r \<in> green_vertical_left R a u v \<Longrightarrow>
      s \<in> green_vertical_left R a u v \<Longrightarrow> r = s"
    "\<And>r s. r \<in> green_vertical_right R a u v \<Longrightarrow>
      s \<in> green_vertical_right R a u v \<Longrightarrow> r = s"
proof -
  fix r s
  assume r: "r \<in> green_vertical_left R a u v"
    and s: "s \<in> green_vertical_left R a u v"
  have xx: "max (Re (fst r)) (Re (fst s)) <
      min (Re (snd r)) (Re (snd s))"
    using r s by (auto simp: green_vertical_left_def; linarith)
  have yy: "max (Im (fst r)) (Im (fst s)) <
      min (Im (snd r)) (Im (snd s))"
    using r s uv by (auto simp: green_vertical_left_def; linarith)
  show "r = s"
    by (rule green_rectangles_no_open_overlap[OF div _ _ xx yy])
      (use r s in \<open>auto simp: green_vertical_left_def\<close>)
next
  fix r s
  assume r: "r \<in> green_vertical_right R a u v"
    and s: "s \<in> green_vertical_right R a u v"
  have xx: "max (Re (fst r)) (Re (fst s)) <
      min (Re (snd r)) (Re (snd s))"
    using r s by (auto simp: green_vertical_right_def; linarith)
  have yy: "max (Im (fst r)) (Im (fst s)) <
      min (Im (snd r)) (Im (snd s))"
    using r s uv by (auto simp: green_vertical_right_def; linarith)
  show "r = s"
    by (rule green_rectangles_no_open_overlap[OF div _ _ xx yy])
      (use r s in \<open>auto simp: green_vertical_right_def\<close>)
qed

lemma green_unique_indicator_sum:
  assumes fin: "finite R"
    and unique: "\<And>r s. r \<in> R \<Longrightarrow> s \<in> R \<Longrightarrow>
      P r \<Longrightarrow> P s \<Longrightarrow> r = s"
  shows "(\<Sum>r\<in>R. if P r then (1::int) else 0) =
    (if \<exists>r\<in>R. P r then 1 else 0)"
proof (cases "\<exists>r\<in>R. P r")
  case False
  then show ?thesis by simp
next
  case True
  then obtain r where r: "r \<in> R" "P r" by blast
  have eq: "P s \<longleftrightarrow> s = r" if "s \<in> R" for s
    using unique[OF that r(1) _ r(2)] r(2) by auto
  have "(\<Sum>s\<in>R. if P s then (1::int) else 0) =
      (\<Sum>s\<in>R. if s = r then 1 else 0)"
    by (rule sum.cong[OF refl]) (use eq in auto)
  then show ?thesis using fin r True by simp
qed

lemma green_signed_side_sum:
  assumes fin: "finite R"
    and A: "\<And>r s. r \<in> R \<Longrightarrow> s \<in> R \<Longrightarrow>
      A r \<Longrightarrow> A s \<Longrightarrow> r = s"
    and B: "\<And>r s. r \<in> R \<Longrightarrow> s \<in> R \<Longrightarrow>
      B r \<Longrightarrow> B s \<Longrightarrow> r = s"
  shows "(\<Sum>r\<in>R. (if A r then (1::int) else 0) -
      (if B r then 1 else 0)) =
    (if \<exists>r\<in>R. A r then 1 else 0) -
    (if \<exists>r\<in>R. B r then 1 else 0)"
  using green_unique_indicator_sum[OF fin A]
    green_unique_indicator_sum[OF fin B]
  by (simp add: sum_subtractf)

lemma green_horizontal_cell_sides:
  assumes "green_rectangular_division R" "r \<in> R" "u < v"
  shows "green_horizontal_cell_coefficient r c u v =
    (if r \<in> green_horizontal_above R c u v then 1 else 0) -
    (if r \<in> green_horizontal_below R c u v then 1 else 0)"
proof -
  have order: "Im (fst r) \<le> Im (snd r)"
    using assms by (auto simp: green_rectangular_division_def)
  show ?thesis
    using assms order
    by (auto simp: green_horizontal_cell_coefficient_def
      green_horizontal_above_def green_horizontal_below_def
      split: if_splits; linarith)
qed

lemma green_vertical_cell_sides:
  assumes "green_rectangular_division R" "r \<in> R" "u < v"
  shows "green_vertical_cell_coefficient r a u v =
    (if r \<in> green_vertical_left R a u v then 1 else 0) -
    (if r \<in> green_vertical_right R a u v then 1 else 0)"
proof -
  have order: "Re (fst r) \<le> Re (snd r)"
    using assms by (auto simp: green_rectangular_division_def)
  show ?thesis
    using assms order
    by (auto simp: green_vertical_cell_coefficient_def
      green_vertical_left_def green_vertical_right_def
      split: if_splits; linarith)
qed

lemma green_horizontal_coefficient_occupancy:
  assumes div: "green_rectangular_division R"
    and atom: "(u,v) \<in> set (green_x_atoms R)"
  shows "green_horizontal_atom_coefficient R c u v =
    (if green_horizontal_above R c u v \<noteq> {} then 1 else 0) -
    (if green_horizontal_below R c u v \<noteq> {} then 1 else 0)"
proof -
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have uv: "u < v" using green_atomic_segments(1)[OF fin atom] by simp
  have eq: "green_horizontal_atom_coefficient R c u v =
      (\<Sum>r\<in>R. (if r \<in> green_horizontal_above R c u v then 1 else 0) -
        (if r \<in> green_horizontal_below R c u v then 1 else 0))"
    unfolding green_horizontal_atom_coefficient_def
    by (rule sum.cong[OF refl]) (rule green_horizontal_cell_sides[OF div _ uv])
  have unique_above: "\<And>r s. r \<in> R \<Longrightarrow> s \<in> R \<Longrightarrow>
      r \<in> green_horizontal_above R c u v \<Longrightarrow>
      s \<in> green_horizontal_above R c u v \<Longrightarrow> r = s"
    by (rule green_horizontal_side_unique(2)[OF div uv])
  have unique_below: "\<And>r s. r \<in> R \<Longrightarrow> s \<in> R \<Longrightarrow>
      r \<in> green_horizontal_below R c u v \<Longrightarrow>
      s \<in> green_horizontal_below R c u v \<Longrightarrow> r = s"
    by (rule green_horizontal_side_unique(1)[OF div uv])
  have above: "(\<exists>r\<in>R. r \<in> green_horizontal_above R c u v) \<longleftrightarrow>
      green_horizontal_above R c u v \<noteq> {}"
    unfolding green_horizontal_above_def by blast
  have below: "(\<exists>r\<in>R. r \<in> green_horizontal_below R c u v) \<longleftrightarrow>
      green_horizontal_below R c u v \<noteq> {}"
    unfolding green_horizontal_below_def by blast
  show ?thesis
    using eq green_signed_side_sum[OF fin unique_above unique_below]
      above below
    by simp
qed

lemma green_vertical_coefficient_occupancy:
  assumes div: "green_rectangular_division R"
    and atom: "(u,v) \<in> set (green_y_atoms R)"
  shows "green_vertical_atom_coefficient R a u v =
    (if green_vertical_left R a u v \<noteq> {} then 1 else 0) -
    (if green_vertical_right R a u v \<noteq> {} then 1 else 0)"
proof -
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have uv: "u < v" using green_atomic_segments(2)[OF fin atom] by simp
  have eq: "green_vertical_atom_coefficient R a u v =
      (\<Sum>r\<in>R. (if r \<in> green_vertical_left R a u v then 1 else 0) -
        (if r \<in> green_vertical_right R a u v then 1 else 0))"
    unfolding green_vertical_atom_coefficient_def
    by (rule sum.cong[OF refl]) (rule green_vertical_cell_sides[OF div _ uv])
  have unique_left: "\<And>r s. r \<in> R \<Longrightarrow> s \<in> R \<Longrightarrow>
      r \<in> green_vertical_left R a u v \<Longrightarrow>
      s \<in> green_vertical_left R a u v \<Longrightarrow> r = s"
    by (rule green_vertical_side_unique(1)[OF div uv])
  have unique_right: "\<And>r s. r \<in> R \<Longrightarrow> s \<in> R \<Longrightarrow>
      r \<in> green_vertical_right R a u v \<Longrightarrow>
      s \<in> green_vertical_right R a u v \<Longrightarrow> r = s"
    by (rule green_vertical_side_unique(2)[OF div uv])
  have left: "(\<exists>r\<in>R. r \<in> green_vertical_left R a u v) \<longleftrightarrow>
      green_vertical_left R a u v \<noteq> {}"
    unfolding green_vertical_left_def by blast
  have right: "(\<exists>r\<in>R. r \<in> green_vertical_right R a u v) \<longleftrightarrow>
      green_vertical_right R a u v \<noteq> {}"
    unfolding green_vertical_right_def by blast
  show ?thesis
    using eq green_signed_side_sum[OF fin unique_left unique_right]
      left right
    by simp
qed

lemma green_signed_presence_cases:
  fixes A B :: bool
  shows "((if A then (1::int) else 0) - (if B then 1 else 0)) \<in> {-1, 0, 1}"
    "((if A then (1::int) else 0) - (if B then 1 else 0) = 1)
      \<longleftrightarrow> A \<and> \<not> B"
    "((if A then (1::int) else 0) - (if B then 1 else 0) = -1)
      \<longleftrightarrow> \<not> A \<and> B"
    "((if A then (1::int) else 0) - (if B then 1 else 0) \<noteq> 0)
      \<longleftrightarrow> (A \<noteq> B)"
  by (cases A; cases B) auto

text \<open>Positive horizontal edges run left to right, with the region above.
  Negative horizontal edges run right to left, with the region below.\<close>
theorem green_horizontal_atom_orientation:
  assumes div: "green_rectangular_division R"
    and atom: "(u,v) \<in> set (green_x_atoms R)"
  shows "green_horizontal_atom_coefficient R c u v \<in> {-1, 0, 1}"
    "green_horizontal_atom_coefficient R c u v = 1 \<longleftrightarrow>
      green_horizontal_above R c u v \<noteq> {} \<and>
      green_horizontal_below R c u v = {}"
    "green_horizontal_atom_coefficient R c u v = -1 \<longleftrightarrow>
      green_horizontal_above R c u v = {} \<and>
      green_horizontal_below R c u v \<noteq> {}"
    "green_horizontal_atom_coefficient R c u v \<noteq> 0 \<longleftrightarrow>
      (green_horizontal_above R c u v \<noteq> {}) \<noteq>
      (green_horizontal_below R c u v \<noteq> {})"
  using green_signed_presence_cases[
    of "green_horizontal_above R c u v \<noteq> {}"
       "green_horizontal_below R c u v \<noteq> {}"]
  by (simp_all add: green_horizontal_coefficient_occupancy[OF div atom])

text \<open>Positive vertical edges run bottom to top, with the region on
  the left. Negative vertical edges run top to bottom, with the region
  on the right.\<close>
theorem green_vertical_atom_orientation:
  assumes div: "green_rectangular_division R"
    and atom: "(u,v) \<in> set (green_y_atoms R)"
  shows "green_vertical_atom_coefficient R a u v \<in> {-1, 0, 1}"
    "green_vertical_atom_coefficient R a u v = 1 \<longleftrightarrow>
      green_vertical_left R a u v \<noteq> {} \<and>
      green_vertical_right R a u v = {}"
    "green_vertical_atom_coefficient R a u v = -1 \<longleftrightarrow>
      green_vertical_left R a u v = {} \<and>
      green_vertical_right R a u v \<noteq> {}"
    "green_vertical_atom_coefficient R a u v \<noteq> 0 \<longleftrightarrow>
      (green_vertical_left R a u v \<noteq> {}) \<noteq>
      (green_vertical_right R a u v \<noteq> {})"
  using green_signed_presence_cases[
    of "green_vertical_left R a u v \<noteq> {}"
       "green_vertical_right R a u v \<noteq> {}"]
  by (simp_all add: green_vertical_coefficient_occupancy[OF div atom])

end
