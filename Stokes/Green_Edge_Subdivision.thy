theory Green_Edge_Subdivision
  imports Green_Rectangular_Union
begin

text \<open>All rectangle coordinates are collected as global cuts. Consecutive
  cuts define elementary horizontal and vertical segments. Their signed
  coefficients add across cells, so shared segments, including those at
  T-junctions, disappear from the filtered boundary sum.\<close>

fun green_adjacent_pairs :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "green_adjacent_pairs [] = []"
| "green_adjacent_pairs [a] = []"
| "green_adjacent_pairs (a # b # xs) = (a,b) # green_adjacent_pairs (b # xs)"

lemmas green_adjacent_pairs_induct [case_names empty singleton step] = green_adjacent_pairs.induct

lemma green_adjacent_pairs_endpoints:
  assumes "(u,v) \<in> set (green_adjacent_pairs xs)"
  shows "u \<in> set xs" "v \<in> set xs"
  using assms by (induction xs rule: green_adjacent_pairs.induct) auto

lemma green_interval_sum_selected:
  fixes f :: "real \<Rightarrow> real"
  assumes "sorted xs" "distinct xs" "a \<in> set xs" "b \<in> set xs"
    "a \<le> b" "continuous_on {a..b} f"
  shows "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs xs.
      if a \<le> u \<and> v \<le> b then integral {u..v} f else 0) = integral {a..b} f"
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
  have x_le: "x \<le> z" if "z \<in> set (y # xs)" for z
    using step.prems(1) that by auto
  show ?case
  proof (cases "a = x")
    case True
    show ?thesis
    proof (cases "b = x")
      case True
      have vgt: "x < v" if "(u,v) \<in> set (green_adjacent_pairs (y # xs))" for u v
        using green_adjacent_pairs_endpoints(2)[OF that] step.prems(1) xy by auto
      have termzero: "(case q of (u,v) \<Rightarrow>
          if a \<le> u \<and> v \<le> b then integral {u..v} f else 0) = 0"
        if "q \<in> set (green_adjacent_pairs (y # xs))" for q
      proof (cases q)
        case (Pair u v)
        have "x < v" using vgt[of u v] that Pair by simp
        then show ?thesis using Pair True \<open>a = x\<close> by simp
      qed
      have zero: "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs (y # xs).
          if a \<le> u \<and> v \<le> b then integral {u..v} f else 0) = 0"
        by (rule sum_list_neutral) (use termzero in auto)
      show ?thesis using True \<open>a = x\<close> zero xy by simp
    next
      case False
      have yin: "y \<le> b" using step.prems(1,4,5) False \<open>a = x\<close> by auto
      have bin: "b \<in> set (y # xs)" using step.prems(4) False by simp
      have cont: "continuous_on {y..b} f"
        using step.prems(6) xy yin \<open>a = x\<close>
        by (auto intro: continuous_on_subset)
      have tail: "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs (y # xs).
          if y \<le> u \<and> v \<le> b then integral {u..v} f else 0) =
        integral {y..b} f"
        using step.IH[of y b] step.prems(1,2) bin yin cont by simp
      have uge: "y \<le> u" if "(u,v) \<in> set (green_adjacent_pairs (y # xs))" for u v
        using green_adjacent_pairs_endpoints(1)[OF that] step.prems(1) by auto
      have eqterm: "(case q of (u,v) \<Rightarrow>
          if a \<le> u \<and> v \<le> b then integral {u..v} f else 0) =
        (case q of (u,v) \<Rightarrow>
          if y \<le> u \<and> v \<le> b then integral {u..v} f else 0)"
        if "q \<in> set (green_adjacent_pairs (y # xs))" for q
      proof (cases q)
        case (Pair u v)
        have "y \<le> u" using uge[of u v] that Pair by simp
        then show ?thesis using Pair \<open>a = x\<close> xy by simp
      qed
      have equiv: "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs (y # xs).
          if a \<le> u \<and> v \<le> b then integral {u..v} f else 0) =
        (\<Sum>(u,v)\<leftarrow>green_adjacent_pairs (y # xs).
          if y \<le> u \<and> v \<le> b then integral {u..v} f else 0)"
        by (intro arg_cong[where f=sum_list] map_cong) (use eqterm in auto)
      have integ: "f integrable_on {a..b}"
        using step.prems(6) by (auto intro: integrable_continuous_real)
      have split: "integral {a..b} f = integral {a..y} f + integral {y..b} f"
        by (rule Henstock_Kurzweil_Integration.integral_combine
          [OF _ yin integ, symmetric]) (use xy \<open>a = x\<close> in auto)
      show ?thesis using tail equiv split xy yin \<open>a = x\<close> by simp
    qed
  next
    case False
    have ain: "a \<in> set (y # xs)" using step.prems(3) False by simp
    have xle_a: "x \<le> a" using ain x_le by blast
    have xa: "x < a" using xle_a False by linarith
    have bin: "b \<in> set (y # xs)"
      using step.prems(4,5) xa by auto
    have tail: "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs (y # xs).
        if a \<le> u \<and> v \<le> b then integral {u..v} f else 0) =
      integral {a..b} f"
      using step.IH[of a b] step.prems ain bin by simp
    show ?thesis using tail xa by simp
  qed
qed

definition green_x_cuts :: "green_rectangle set \<Rightarrow> real set" where
  "green_x_cuts R = (\<Union>r\<in>R. {Re (fst r), Re (snd r)})"

definition green_y_cuts :: "green_rectangle set \<Rightarrow> real set" where
  "green_y_cuts R = (\<Union>r\<in>R. {Im (fst r), Im (snd r)})"

definition green_x_atoms :: "green_rectangle set \<Rightarrow> (real \<times> real) list" where
  "green_x_atoms R = green_adjacent_pairs (sorted_list_of_set (green_x_cuts R))"

definition green_y_atoms :: "green_rectangle set \<Rightarrow> (real \<times> real) list" where
  "green_y_atoms R = green_adjacent_pairs (sorted_list_of_set (green_y_cuts R))"

lemma green_cuts_finite:
  assumes "finite R"
  shows "finite (green_x_cuts R)" "finite (green_y_cuts R)"
  using assms by (auto simp: green_x_cuts_def green_y_cuts_def)

lemma green_adjacent_pairs_order:
  assumes "sorted xs" "(u,v) \<in> set (green_adjacent_pairs xs)"
  shows "u \<le> v"
  using assms by (induction xs rule: green_adjacent_pairs_induct) auto

lemma green_adjacent_pairs_strict:
  assumes "sorted xs" "distinct xs" "(u,v) \<in> set (green_adjacent_pairs xs)"
  shows "u < v"
  using assms by (induction xs rule: green_adjacent_pairs_induct) auto

lemma green_adjacent_pairs_no_cut:
  assumes "sorted xs" "(u,v) \<in> set (green_adjacent_pairs xs)"
    "w \<in> set xs" "u < w" "w < v"
  shows False
  using assms
proof (induction xs rule: green_adjacent_pairs_induct)
  case empty
  then show ?case by simp
next
  case (singleton x)
  then show ?case by simp
next
  case (step x y ys)
  show ?case
  proof (cases "(u,v) = (x,y)")
    case True
    have "w = x \<or> w \<in> set (y # ys)" using step.prems(3) by simp
    moreover have "y \<le> w" if "w \<in> set (y # ys)"
      using step.prems(1) that by auto
    ultimately show ?thesis using True step.prems(4,5) by auto
  next
    case False
    have cases: "(u,v) = (x,y) \<or>
        (u,v) \<in> set (green_adjacent_pairs (y # ys))"
      using step.prems(2) by simp
    have atom: "(u,v) \<in> set (green_adjacent_pairs (y # ys))"
      using cases False by blast
    have sorted: "sorted (y # ys)" using step.prems(1) by simp
    have wtail: "w \<in> set (y # ys)"
    proof (rule ccontr)
      assume "w \<notin> set (y # ys)"
      then have wx: "w = x" using step.prems(3) by simp
      have utail: "u \<in> set (y # ys)"
        using green_adjacent_pairs_endpoints(1)[OF atom] .
      have "x \<le> u" using step.prems(1) utail by auto
      then show False using wx step.prems(4) by order
    qed
    show ?thesis by (rule step.IH[OF sorted atom wtail step.prems(4,5)])
  qed
qed

lemma green_cut_atoms:
  assumes fin: "finite C"
    and atom: "(u,v) \<in> set (green_adjacent_pairs (sorted_list_of_set C))"
  shows "u < v" "\<And>w. w \<in> C \<Longrightarrow> w \<le> u \<or> v \<le> w"
proof -
  let ?xs = "sorted_list_of_set C"
  have sorted: "sorted ?xs" and distinct: "distinct ?xs" using fin by simp_all
  show "u < v" by (rule green_adjacent_pairs_strict[OF sorted distinct atom])
  fix w assume w: "w \<in> C"
  have wset: "w \<in> set ?xs" using fin w by simp
  have no: "\<not> (u < w \<and> w < v)"
  proof
    assume both: "u < w \<and> w < v"
    have uw: "u < w" and wv: "w < v" using both by auto
    show False by (rule green_adjacent_pairs_no_cut[OF sorted atom wset uw wv])
  qed
  show "w \<le> u \<or> v \<le> w" using no by (auto simp: not_le)
qed

lemma green_atomic_segments:
  assumes "finite R"
  shows "(u,v) \<in> set (green_x_atoms R) \<Longrightarrow>
      u < v \<and> (\<forall>w\<in>green_x_cuts R. w \<le> u \<or> v \<le> w)"
    "(u,v) \<in> set (green_y_atoms R) \<Longrightarrow>
      u < v \<and> (\<forall>w\<in>green_y_cuts R. w \<le> u \<or> v \<le> w)"
  using assms green_cut_atoms[OF green_cuts_finite(1)[OF assms]]
    green_cut_atoms[OF green_cuts_finite(2)[OF assms]]
  by (auto simp: green_x_atoms_def green_y_atoms_def)

lemma green_line_integral_eq:
  fixes f :: "real \<Rightarrow> real"
  assumes "continuous_on {a..b} f"
  shows "(LINT x:{a..b}|lborel. f x) = integral {a..b} f"
proof (rule set_borel_integral_eq_integral(2))
  show "set_integrable lborel {a..b} f"
    unfolding set_integrable_def
    by (rule borel_integrable_compact) (use assms in auto)
qed

lemma green_cut_interval_sum:
  fixes f :: "real \<Rightarrow> real"
  assumes "finite C" "a \<in> C" "b \<in> C" "a \<le> b"
    "continuous_on {a..b} f"
  shows "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs (sorted_list_of_set C).
      if a \<le> u \<and> v \<le> b then (LINT x:{u..v}|lborel. f x) else 0) =
    (LINT x:{a..b}|lborel. f x)"
proof -
  let ?xs = "sorted_list_of_set C"
  have sorted: "sorted ?xs" using assms(1) by simp
  have distinct: "distinct ?xs" using assms(1) by simp
  have ain: "a \<in> set ?xs" and bin: "b \<in> set ?xs"
    using assms(1-3) by auto
  have eq: "(LINT x:{u..v}|lborel. f x) = integral {u..v} f"
    if "(u,v) \<in> set (green_adjacent_pairs ?xs)" "a \<le> u" "v \<le> b"
    for u v
  proof -
    have uv: "u \<le> v" using green_adjacent_pairs_order[OF sorted that(1)] .
    have "continuous_on {u..v} f"
      using assms(5) that(2,3) uv
      by (auto intro: continuous_on_subset)
    then show ?thesis by (rule green_line_integral_eq)
  qed
  have rewrite: "(\<Sum>(u,v)\<leftarrow>green_adjacent_pairs ?xs.
      if a \<le> u \<and> v \<le> b then (LINT x:{u..v}|lborel. f x) else 0) =
    (\<Sum>(u,v)\<leftarrow>green_adjacent_pairs ?xs.
      if a \<le> u \<and> v \<le> b then integral {u..v} f else 0)"
    by (intro arg_cong[where f=sum_list] map_cong)
      (use eq in \<open>auto split: prod.splits\<close>)
  show ?thesis
    using rewrite green_interval_sum_selected[OF sorted distinct ain bin assms(4,5)]
      green_line_integral_eq[OF assms(5)]
    by simp
qed

lemma green_sum_list_pair_subtract:
  fixes f g :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::ab_group_add"
  shows "(\<Sum>(u,v)\<leftarrow>xs. f u v - g u v) =
    (\<Sum>(u,v)\<leftarrow>xs. f u v) - (\<Sum>(u,v)\<leftarrow>xs. g u v)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons p xs)
  obtain u v where p: "p = (u,v)" by (cases p) auto
  show ?case using Cons.IH by (simp add: p algebra_simps)
qed

lemma green_sum_line_atoms_swap_pair:
  "(\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>ts. \<Sum>r\<in>R. f r l u v) =
    (\<Sum>r\<in>R. \<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>ts. f r l u v)"
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons p ts)
  obtain u v where p: "p = (u,v)" by (cases p) auto
  have swap: "(\<Sum>l\<in>L. \<Sum>r\<in>R. f r l u v) =
    (\<Sum>r\<in>R. \<Sum>l\<in>L. f r l u v)"
    by (rule sum.swap)
  show ?case using Cons.IH swap
    by (simp add: p sum.distrib algebra_simps)
qed

lemma green_sum_list_pair_of_int:
  fixes k :: "'r \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> int"
    and I :: "'a \<Rightarrow> 'b \<Rightarrow> real"
  shows "(\<Sum>(u,v)\<leftarrow>ts. of_int (\<Sum>r\<in>R. k r u v) * I u v) =
    (\<Sum>(u,v)\<leftarrow>ts. \<Sum>r\<in>R. of_int (k r u v) * I u v)"
proof -
  have point: "of_int (\<Sum>r\<in>R. k r u v) * I u v =
    (\<Sum>r\<in>R. of_int (k r u v) * I u v)" for u v
    by (simp add: sum_distrib_right)
  show ?thesis
    by (intro arg_cong[where f=sum_list] map_cong)
      (use point in \<open>auto split: prod.splits\<close>)
qed

lemma green_signed_indicator:
  "of_int ((if A then 1 else 0) - (if B then 1 else 0)) * (x::'a::ring_1) =
    (if A then x else 0) - (if B then x else 0)"
  by (cases A; cases B) simp_all

lemma green_axis_indicator_sum:
  fixes F :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes "finite L" "c \<in> L" "finite C" "a \<in> C" "b \<in> C" "a \<le> b"
    "continuous_on {a..b} (F c)"
  shows "(\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>green_adjacent_pairs (sorted_list_of_set C).
      if l = c \<and> a \<le> u \<and> v \<le> b then
        (LINT x:{u..v}|lborel. F l x) else 0) =
    (LINT x:{a..b}|lborel. F c x)"
proof -
  let ?atoms = "green_adjacent_pairs (sorted_list_of_set C)"
  have line: "(\<Sum>(u,v)\<leftarrow>?atoms.
      if l = c \<and> a \<le> u \<and> v \<le> b then
        (LINT x:{u..v}|lborel. F l x) else 0) =
    (if l = c then (\<Sum>(u,v)\<leftarrow>?atoms.
      if a \<le> u \<and> v \<le> b then
        (LINT x:{u..v}|lborel. F c x) else 0) else 0)" for l
  proof (cases "l = c")
    case True
    then show ?thesis by (subst True) simp
  next
    case False
    have Z: "(\<Sum>(u,v)\<leftarrow>?atoms. (0::real)) = 0"
      by (rule sum_list_neutral) auto
    show ?thesis using False Z by simp
  qed
  have "(\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>?atoms.
      if l = c \<and> a \<le> u \<and> v \<le> b then
        (LINT x:{u..v}|lborel. F l x) else 0) =
    (\<Sum>l\<in>L. if l = c then (\<Sum>(u,v)\<leftarrow>?atoms.
      if a \<le> u \<and> v \<le> b then
        (LINT x:{u..v}|lborel. F c x) else 0) else 0)"
    by (rule sum.cong[OF refl]) (rule line)
  also have "\<dots> = (\<Sum>(u,v)\<leftarrow>?atoms.
      if a \<le> u \<and> v \<le> b then
        (LINT x:{u..v}|lborel. F c x) else 0)"
    using assms(1,2) by simp
  also have "\<dots> = (LINT x:{a..b}|lborel. F c x)"
    using green_cut_interval_sum[OF assms(3-7)] by simp
  finally show ?thesis .
qed

lemma green_axis_signed_sum:
  fixes F :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes "finite L" "c \<in> L" "d \<in> L" "finite C" "a \<in> C" "b \<in> C"
    "a \<le> b" "continuous_on {a..b} (F c)" "continuous_on {a..b} (F d)"
  shows "(\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>green_adjacent_pairs (sorted_list_of_set C).
      of_int ((if l = c \<and> a \<le> u \<and> v \<le> b then 1 else 0) -
        (if l = d \<and> a \<le> u \<and> v \<le> b then 1 else 0)) *
      (LINT x:{u..v}|lborel. F l x)) =
    (LINT x:{a..b}|lborel. F c x) - (LINT x:{a..b}|lborel. F d x)"
proof -
  let ?atoms = "green_adjacent_pairs (sorted_list_of_set C)"
  have point: "of_int ((if l = c \<and> a \<le> u \<and> v \<le> b then 1 else 0) -
        (if l = d \<and> a \<le> u \<and> v \<le> b then 1 else 0)) *
      (LINT x:{u..v}|lborel. F l x) =
    (if l = c \<and> a \<le> u \<and> v \<le> b then
      (LINT x:{u..v}|lborel. F l x) else 0) -
    (if l = d \<and> a \<le> u \<and> v \<le> b then
      (LINT x:{u..v}|lborel. F l x) else 0)" for l u v
    by (rule green_signed_indicator)
  have inner: "(\<Sum>(u,v)\<leftarrow>?atoms.
      of_int ((if l = c \<and> a \<le> u \<and> v \<le> b then 1 else 0) -
        (if l = d \<and> a \<le> u \<and> v \<le> b then 1 else 0)) *
      (LINT x:{u..v}|lborel. F l x)) =
    (\<Sum>(u,v)\<leftarrow>?atoms. if l = c \<and> a \<le> u \<and> v \<le> b then
      (LINT x:{u..v}|lborel. F l x) else 0) -
    (\<Sum>(u,v)\<leftarrow>?atoms. if l = d \<and> a \<le> u \<and> v \<le> b then
      (LINT x:{u..v}|lborel. F l x) else 0)" for l
  proof -
    have rewrite: "(\<Sum>(u,v)\<leftarrow>?atoms.
        of_int ((if l = c \<and> a \<le> u \<and> v \<le> b then 1 else 0) -
          (if l = d \<and> a \<le> u \<and> v \<le> b then 1 else 0)) *
        (LINT x:{u..v}|lborel. F l x)) =
      (\<Sum>(u,v)\<leftarrow>?atoms.
        (if l = c \<and> a \<le> u \<and> v \<le> b then
          (LINT x:{u..v}|lborel. F l x) else 0) -
        (if l = d \<and> a \<le> u \<and> v \<le> b then
          (LINT x:{u..v}|lborel. F l x) else 0))"
      by (intro arg_cong[where f=sum_list] map_cong)
        (use point in \<open>auto split: prod.splits\<close>)
    show ?thesis using rewrite by (simp add: green_sum_list_pair_subtract)
  qed
  have "(\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>?atoms.
      of_int ((if l = c \<and> a \<le> u \<and> v \<le> b then 1 else 0) -
        (if l = d \<and> a \<le> u \<and> v \<le> b then 1 else 0)) *
      (LINT x:{u..v}|lborel. F l x)) =
    (\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>?atoms. if l = c \<and> a \<le> u \<and> v \<le> b then
      (LINT x:{u..v}|lborel. F l x) else 0) -
    (\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>?atoms. if l = d \<and> a \<le> u \<and> v \<le> b then
      (LINT x:{u..v}|lborel. F l x) else 0)"
  proof -
    have rewrite: "(\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>?atoms.
        of_int ((if l = c \<and> a \<le> u \<and> v \<le> b then 1 else 0) -
          (if l = d \<and> a \<le> u \<and> v \<le> b then 1 else 0)) *
        (LINT x:{u..v}|lborel. F l x)) =
      (\<Sum>l\<in>L.
        (\<Sum>(u,v)\<leftarrow>?atoms. if l = c \<and> a \<le> u \<and> v \<le> b then
          (LINT x:{u..v}|lborel. F l x) else 0) -
        (\<Sum>(u,v)\<leftarrow>?atoms. if l = d \<and> a \<le> u \<and> v \<le> b then
          (LINT x:{u..v}|lborel. F l x) else 0))"
      by (rule sum.cong[OF refl]) (rule inner)
    show ?thesis using rewrite by (simp add: sum_subtractf)
  qed
  also have "\<dots> = (LINT x:{a..b}|lborel. F c x) - (LINT x:{a..b}|lborel. F d x)"
  proof -
    have pos: "(\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>?atoms.
        if l = c \<and> a \<le> u \<and> v \<le> b then
          (LINT x:{u..v}|lborel. F l x) else 0) =
      (LINT x:{a..b}|lborel. F c x)"
      by (rule green_axis_indicator_sum) (use assms in auto)
    have neg: "(\<Sum>l\<in>L. \<Sum>(u,v)\<leftarrow>?atoms.
        if l = d \<and> a \<le> u \<and> v \<le> b then
          (LINT x:{u..v}|lborel. F l x) else 0) =
      (LINT x:{a..b}|lborel. F d x)"
      by (rule green_axis_indicator_sum) (use assms in auto)
    show ?thesis using pos neg by simp
  qed
  finally show ?thesis .
qed

definition green_horizontal_cell_coefficient ::
    "green_rectangle \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int" where
  "green_horizontal_cell_coefficient r c u v =
    (if c = Im (fst r) \<and> Re (fst r) \<le> u \<and> v \<le> Re (snd r) then 1 else 0) -
    (if c = Im (snd r) \<and> Re (fst r) \<le> u \<and> v \<le> Re (snd r) then 1 else 0)"

definition green_vertical_cell_coefficient ::
    "green_rectangle \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int" where
  "green_vertical_cell_coefficient r a u v =
    (if a = Re (snd r) \<and> Im (fst r) \<le> u \<and> v \<le> Im (snd r) then 1 else 0) -
    (if a = Re (fst r) \<and> Im (fst r) \<le> u \<and> v \<le> Im (snd r) then 1 else 0)"

definition green_horizontal_atom_coefficient ::
    "green_rectangle set \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int" where
  "green_horizontal_atom_coefficient R c u v =
    (\<Sum>r\<in>R. green_horizontal_cell_coefficient r c u v)"

definition green_vertical_atom_coefficient ::
    "green_rectangle set \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int" where
  "green_vertical_atom_coefficient R a u v =
    (\<Sum>r\<in>R. green_vertical_cell_coefficient r a u v)"

lemma green_T_junction_vertical_cancels:
  assumes "a < b" "b < f" "c < d" "d < e"
  defines "R \<equiv> {(Complex a c, Complex b e),
    (Complex b c, Complex f d), (Complex b d, Complex f e)}"
  shows "green_vertical_atom_coefficient R b c d = 0"
    "green_vertical_atom_coefficient R b d e = 0"
  using assms
  by (simp_all add: green_vertical_atom_coefficient_def
    green_vertical_cell_coefficient_def)

lemma green_T_junction_horizontal_cancels:
  assumes "a < b" "b < f" "c < d" "d < e"
  defines "R \<equiv> {(Complex a c, Complex f d),
    (Complex a d, Complex b e), (Complex b d, Complex f e)}"
  shows "green_horizontal_atom_coefficient R d a b = 0"
    "green_horizontal_atom_coefficient R d b f = 0"
  using assms
  by (simp_all add: green_horizontal_atom_coefficient_def
    green_horizontal_cell_coefficient_def)

lemma green_rectangular_C1_cell:
  assumes "green_rectangular_C1 P Q R" "r \<in> R"
  shows "green_rectangle_C1 P Q
    (Re (fst r)) (Re (snd r)) (Im (fst r)) (Im (snd r))"
  using assms
  by (auto simp: green_rectangular_C1_def green_rectangular_region_def
    green_rectangle_set_def green_rectangle_C1_def cbox_Pair_eq)

lemma green_rectangle_subdivided:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R" and r: "r \<in> R"
  shows "(\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_x_atoms R.
      of_int (green_horizontal_cell_coefficient r c u v) *
        green_edge_integral P Q (Horizontal u v c)) +
    (\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_y_atoms R.
      of_int (green_vertical_cell_coefficient r a u v) *
        green_edge_integral P Q (Vertical u v a)) =
    green_rectangle_boundary_integral P Q r"
proof -
  let ?a = "Re (fst r)" and ?b = "Re (snd r)"
  let ?c = "Im (fst r)" and ?d = "Im (snd r)"
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have xy: "?a \<le> ?b" "?c \<le> ?d"
    using div r by (auto simp: green_rectangular_division_def)
  have fins: "finite (green_x_cuts R)" "finite (green_y_cuts R)"
    by (rule green_cuts_finite[OF fin])+
  have xin: "?a \<in> green_x_cuts R" "?b \<in> green_x_cuts R"
    using r by (auto simp: green_x_cuts_def)
  have yin: "?c \<in> green_y_cuts R" "?d \<in> green_y_cuts R"
    using r by (auto simp: green_y_cuts_def)
  have cell: "green_rectangle_C1 P Q ?a ?b ?c ?d"
    using green_rectangular_C1_cell[OF C1 r] .
  have PC: "continuous_on ({?a..?b} \<times> {?c..?d}) P"
    using green_rectangle_C1_continuous_on(1)[OF cell] .
  have QC: "continuous_on ({?a..?b} \<times> {?c..?d}) Q"
    using green_rectangle_C1_continuous_on(2)[OF cell] .
  have Pc: "continuous_on {?a..?b} (\<lambda>x. P (x,?c))"
    by (rule continuous_on_compose2[OF PC])
      (use xy in \<open>auto intro!: continuous_intros\<close>)
  have Pd: "continuous_on {?a..?b} (\<lambda>x. P (x,?d))"
    by (rule continuous_on_compose2[OF PC])
      (use xy in \<open>auto intro!: continuous_intros\<close>)
  have Qb: "continuous_on {?c..?d} (\<lambda>y. Q (?b,y))"
    by (rule continuous_on_compose2[OF QC])
      (use xy in \<open>auto intro!: continuous_intros\<close>)
  have Qa: "continuous_on {?c..?d} (\<lambda>y. Q (?a,y))"
    by (rule continuous_on_compose2[OF QC])
      (use xy in \<open>auto intro!: continuous_intros\<close>)
  have horizontal: "(\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_x_atoms R.
      of_int (green_horizontal_cell_coefficient r c u v) *
        green_edge_integral P Q (Horizontal u v c)) =
      (LINT x:{?a..?b}|lborel. P (x,?c)) -
      (LINT x:{?a..?b}|lborel. P (x,?d))"
    using green_axis_signed_sum[of "green_y_cuts R" ?c ?d "green_x_cuts R"
      ?a ?b "\<lambda>c x. P (x,c)", OF fins(2) yin fins(1) xin xy(1) Pc Pd]
    by (simp add: green_x_atoms_def green_horizontal_cell_coefficient_def)
  have vertical: "(\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_y_atoms R.
      of_int (green_vertical_cell_coefficient r a u v) *
        green_edge_integral P Q (Vertical u v a)) =
      (LINT y:{?c..?d}|lborel. Q (?b,y)) -
      (LINT y:{?c..?d}|lborel. Q (?a,y))"
    using green_axis_signed_sum[of "green_x_cuts R" ?b ?a "green_y_cuts R"
      ?c ?d "\<lambda>a y. Q (a,y)", OF fins(1) xin(2) xin(1) fins(2) yin xy(2) Qb Qa]
    by (simp add: green_y_atoms_def green_vertical_cell_coefficient_def)
  show ?thesis using horizontal vertical
    by (simp add: green_rectangle_boundary_integral_def algebra_simps)
qed

definition green_subdivided_boundary_integral ::
    "(real \<times> real \<Rightarrow> real) \<Rightarrow> (real \<times> real \<Rightarrow> real) \<Rightarrow>
      green_rectangle set \<Rightarrow> real" where
  "green_subdivided_boundary_integral P Q R =
    (\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_x_atoms R.
      of_int (green_horizontal_atom_coefficient R c u v) *
        green_edge_integral P Q (Horizontal u v c)) +
    (\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_y_atoms R.
      of_int (green_vertical_atom_coefficient R a u v) *
        green_edge_integral P Q (Vertical u v a))"

definition green_exposed_horizontal_atoms ::
    "green_rectangle set \<Rightarrow> real \<Rightarrow> (real \<times> real) list" where
  "green_exposed_horizontal_atoms R c =
    filter (\<lambda>(u,v). green_horizontal_atom_coefficient R c u v \<noteq> 0)
      (green_x_atoms R)"

definition green_exposed_vertical_atoms ::
    "green_rectangle set \<Rightarrow> real \<Rightarrow> (real \<times> real) list" where
  "green_exposed_vertical_atoms R a =
    filter (\<lambda>(u,v). green_vertical_atom_coefficient R a u v \<noteq> 0)
      (green_y_atoms R)"

lemma green_subdivided_boundary_exposed:
  "green_subdivided_boundary_integral P Q R =
    (\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_exposed_horizontal_atoms R c.
      of_int (green_horizontal_atom_coefficient R c u v) *
        green_edge_integral P Q (Horizontal u v c)) +
    (\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_exposed_vertical_atoms R a.
      of_int (green_vertical_atom_coefficient R a u v) *
        green_edge_integral P Q (Vertical u v a))"
proof -
  have h: "(\<Sum>(u,v)\<leftarrow>green_x_atoms R.
      of_int (green_horizontal_atom_coefficient R c u v) *
        green_edge_integral P Q (Horizontal u v c)) =
    (\<Sum>(u,v)\<leftarrow>green_exposed_horizontal_atoms R c.
      of_int (green_horizontal_atom_coefficient R c u v) *
        green_edge_integral P Q (Horizontal u v c))" for c
    unfolding green_exposed_horizontal_atoms_def
    by (rule sum_list_map_filter[symmetric]) (auto split: prod.splits)
  have v: "(\<Sum>(u,v)\<leftarrow>green_y_atoms R.
      of_int (green_vertical_atom_coefficient R a u v) *
        green_edge_integral P Q (Vertical u v a)) =
    (\<Sum>(u,v)\<leftarrow>green_exposed_vertical_atoms R a.
      of_int (green_vertical_atom_coefficient R a u v) *
        green_edge_integral P Q (Vertical u v a))" for a
    unfolding green_exposed_vertical_atoms_def
    by (rule sum_list_map_filter[symmetric]) (auto split: prod.splits)
  have H: "(\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_x_atoms R.
      of_int (green_horizontal_atom_coefficient R c u v) *
        green_edge_integral P Q (Horizontal u v c)) =
    (\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_exposed_horizontal_atoms R c.
      of_int (green_horizontal_atom_coefficient R c u v) *
        green_edge_integral P Q (Horizontal u v c))"
    by (rule sum.cong[OF refl]) (rule h)
  have V: "(\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_y_atoms R.
      of_int (green_vertical_atom_coefficient R a u v) *
        green_edge_integral P Q (Vertical u v a)) =
    (\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_exposed_vertical_atoms R a.
      of_int (green_vertical_atom_coefficient R a u v) *
        green_edge_integral P Q (Vertical u v a))"
    by (rule sum.cong[OF refl]) (rule v)
  show ?thesis unfolding green_subdivided_boundary_integral_def using H V by simp
qed

lemma green_subdivided_boundary_eq:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
  shows "green_subdivided_boundary_integral P Q R =
    green_rectangular_boundary_integral P Q R"
proof -
  let ?X = "green_x_cuts R" and ?Y = "green_y_cuts R"
  let ?XA = "green_x_atoms R" and ?YA = "green_y_atoms R"
  let ?H = "\<lambda>r. \<Sum>c\<in>?Y. \<Sum>(u,v)\<leftarrow>?XA.
    of_int (green_horizontal_cell_coefficient r c u v) *
      green_edge_integral P Q (Horizontal u v c)"
  let ?V = "\<lambda>r. \<Sum>a\<in>?X. \<Sum>(u,v)\<leftarrow>?YA.
    of_int (green_vertical_cell_coefficient r a u v) *
      green_edge_integral P Q (Vertical u v a)"
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have H: "(\<Sum>c\<in>?Y. \<Sum>(u,v)\<leftarrow>?XA.
      of_int (green_horizontal_atom_coefficient R c u v) *
        green_edge_integral P Q (Horizontal u v c)) = (\<Sum>r\<in>R. ?H r)"
  proof -
    have "(\<Sum>c\<in>?Y. \<Sum>(u,v)\<leftarrow>?XA.
        of_int (green_horizontal_atom_coefficient R c u v) *
          green_edge_integral P Q (Horizontal u v c)) =
      (\<Sum>c\<in>?Y. \<Sum>(u,v)\<leftarrow>?XA. \<Sum>r\<in>R.
        of_int (green_horizontal_cell_coefficient r c u v) *
          green_edge_integral P Q (Horizontal u v c))"
      unfolding green_horizontal_atom_coefficient_def
      by (rule sum.cong[OF refl]) (rule green_sum_list_pair_of_int)
    also have "\<dots> = (\<Sum>r\<in>R. ?H r)"
      by (rule green_sum_line_atoms_swap_pair)
    finally show ?thesis .
  qed
  have V: "(\<Sum>a\<in>?X. \<Sum>(u,v)\<leftarrow>?YA.
      of_int (green_vertical_atom_coefficient R a u v) *
        green_edge_integral P Q (Vertical u v a)) = (\<Sum>r\<in>R. ?V r)"
  proof -
    have "(\<Sum>a\<in>?X. \<Sum>(u,v)\<leftarrow>?YA.
        of_int (green_vertical_atom_coefficient R a u v) *
          green_edge_integral P Q (Vertical u v a)) =
      (\<Sum>a\<in>?X. \<Sum>(u,v)\<leftarrow>?YA. \<Sum>r\<in>R.
        of_int (green_vertical_cell_coefficient r a u v) *
          green_edge_integral P Q (Vertical u v a))"
      unfolding green_vertical_atom_coefficient_def
      by (rule sum.cong[OF refl]) (rule green_sum_list_pair_of_int)
    also have "\<dots> = (\<Sum>r\<in>R. ?V r)"
      by (rule green_sum_line_atoms_swap_pair)
    finally show ?thesis .
  qed
  have each: "?H r + ?V r = green_rectangle_boundary_integral P Q r"
    if "r \<in> R" for r
    by (rule green_rectangle_subdivided[OF div C1 that])
  have "green_subdivided_boundary_integral P Q R =
      (\<Sum>r\<in>R. ?H r + ?V r)"
    using H V by (simp add: green_subdivided_boundary_integral_def sum.distrib)
  also have "\<dots> = (\<Sum>r\<in>R. green_rectangle_boundary_integral P Q r)"
    by (rule sum.cong[OF refl]) (rule each)
  also have "\<dots> = green_rectangular_boundary_integral P Q R"
    using green_rectangular_boundary_sum[OF fin] by simp
  finally show ?thesis .
qed

theorem Green_rectangular_union_exposed:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
  shows "(LINT p:green_rectangular_region R|lborel.
      frechet_derivative Q (at p) (1,0) -
      frechet_derivative P (at p) (0,1)) =
    (\<Sum>c\<in>green_y_cuts R. \<Sum>(u,v)\<leftarrow>green_exposed_horizontal_atoms R c.
      of_int (green_horizontal_atom_coefficient R c u v) *
        green_edge_integral P Q (Horizontal u v c)) +
    (\<Sum>a\<in>green_x_cuts R. \<Sum>(u,v)\<leftarrow>green_exposed_vertical_atoms R a.
      of_int (green_vertical_atom_coefficient R a u v) *
        green_edge_integral P Q (Vertical u v a))"
  using Green_rectangular_union[OF div C1]
    green_subdivided_boundary_eq[OF div C1]
    green_subdivided_boundary_exposed[of P Q R]
  by simp

end
