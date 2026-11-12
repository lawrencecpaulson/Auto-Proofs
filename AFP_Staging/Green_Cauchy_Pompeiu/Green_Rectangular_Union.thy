theory Green_Rectangular_Union
  imports Green_Rectangle_Contour
begin

text \<open>Rectangles are given by their lower-left and upper-right complex corners.\<close>
type_synonym green_rectangle = "complex \<times> complex"

definition green_rectangle_set :: "green_rectangle \<Rightarrow> (real \<times> real) set" where
  "green_rectangle_set r =
    cbox (Re (fst r), Im (fst r)) (Re (snd r), Im (snd r))"

definition green_rectangle_open :: "green_rectangle \<Rightarrow> (real \<times> real) set" where
  "green_rectangle_open r =
    box (Re (fst r), Im (fst r)) (Re (snd r), Im (snd r))"

definition green_rectangular_region :: "green_rectangle set \<Rightarrow> (real \<times> real) set" where
  "green_rectangular_region R = (\<Union>r\<in>R. green_rectangle_set r)"

definition green_rectangular_division :: "green_rectangle set \<Rightarrow> bool" where
  "green_rectangular_division R \<longleftrightarrow>
    finite R \<and>
    (\<forall>r\<in>R. Re (fst r) \<le> Re (snd r) \<and> Im (fst r) \<le> Im (snd r)) \<and>
    (\<forall>r\<in>R. \<forall>s\<in>R. r \<noteq> s \<longrightarrow>
      green_rectangle_open r \<inter> green_rectangle_open s = {})"

definition green_rectangular_C1 ::
    "(real \<times> real \<Rightarrow> real) \<Rightarrow> (real \<times> real \<Rightarrow> real) \<Rightarrow>
      green_rectangle set \<Rightarrow> bool" where
  "green_rectangular_C1 P Q R \<longleftrightarrow>
    (\<exists>U. green_rectangular_region R \<subseteq> U \<and> Ck_on 1 P U \<and> Ck_on 1 Q U)"

text \<open>The edge sum is an oriented boundary chain. On a common grid, each
  whole internal edge occurs twice with opposite coefficients. At a T-junction,
  an edge must be subdivided to display only the exposed boundary segments.\<close>

datatype green_edge = Horizontal real real real | Vertical real real real

fun green_edge_integral ::
    "(real \<times> real \<Rightarrow> real) \<Rightarrow> (real \<times> real \<Rightarrow> real) \<Rightarrow>
      green_edge \<Rightarrow> real" where
  "green_edge_integral P Q (Horizontal a b c) =
    (LINT x:{a..b}|lborel. P (x,c))"
| "green_edge_integral P Q (Vertical c d a) =
    (LINT y:{c..d}|lborel. Q (a,y))"

definition green_rectangle_edges :: "green_rectangle \<Rightarrow> green_edge set" where
  "green_rectangle_edges r =
    {Horizontal (Re (fst r)) (Re (snd r)) (Im (fst r)),
     Vertical (Im (fst r)) (Im (snd r)) (Re (snd r)),
     Horizontal (Re (fst r)) (Re (snd r)) (Im (snd r)),
     Vertical (Im (fst r)) (Im (snd r)) (Re (fst r))}"

definition green_rectangle_edge_coefficient :: "green_rectangle \<Rightarrow> green_edge \<Rightarrow> int" where
  "green_rectangle_edge_coefficient r e =
    (if e = Horizontal (Re (fst r)) (Re (snd r)) (Im (fst r)) then 1 else 0) +
    (if e = Vertical (Im (fst r)) (Im (snd r)) (Re (snd r)) then 1 else 0) -
    (if e = Horizontal (Re (fst r)) (Re (snd r)) (Im (snd r)) then 1 else 0) -
    (if e = Vertical (Im (fst r)) (Im (snd r)) (Re (fst r)) then 1 else 0)"

definition green_rectangular_edges :: "green_rectangle set \<Rightarrow> green_edge set" where
  "green_rectangular_edges R = (\<Union>r\<in>R. green_rectangle_edges r)"

definition green_rectangular_edge_coefficient :: "green_rectangle set \<Rightarrow> green_edge \<Rightarrow> int" where
  "green_rectangular_edge_coefficient R e =
    (\<Sum>r\<in>R. green_rectangle_edge_coefficient r e)"

definition green_rectangular_boundary_integral ::
    "(real \<times> real \<Rightarrow> real) \<Rightarrow> (real \<times> real \<Rightarrow> real) \<Rightarrow>
      green_rectangle set \<Rightarrow> real" where
  "green_rectangular_boundary_integral P Q R =
    (\<Sum>e\<in>green_rectangular_edges R.
      of_int (green_rectangular_edge_coefficient R e) * green_edge_integral P Q e)"

lemma green_sum_single_edge:
  fixes f :: "green_edge \<Rightarrow> real"
  assumes "finite E" "e0 \<in> E"
  shows "(\<Sum>e\<in>E. f e * real_of_int (if e = e0 then 1 else 0)) = f e0"
proof -
  have "(\<Sum>e\<in>E. f e * real_of_int (if e = e0 then 1 else 0)) =
      (\<Sum>e\<in>E. if e = e0 then f e else 0)"
    by (rule sum.cong) auto
  also have "\<dots> = f e0" using assms by simp
  finally show ?thesis .
qed

definition green_uncancelled_edges :: "green_rectangle set \<Rightarrow> green_edge set" where
  "green_uncancelled_edges R =
    {e \<in> green_rectangular_edges R. green_rectangular_edge_coefficient R e \<noteq> 0}"

lemma green_rectangular_boundary_uncancelled:
  assumes "finite R"
  shows "green_rectangular_boundary_integral P Q R =
    (\<Sum>e\<in>green_uncancelled_edges R.
      of_int (green_rectangular_edge_coefficient R e) * green_edge_integral P Q e)"
  unfolding green_rectangular_boundary_integral_def green_uncancelled_edges_def
  by (rule sum.mono_neutral_right)
    (use assms in \<open>auto simp: green_rectangular_edges_def green_rectangle_edges_def\<close>)

lemma green_shared_vertical_edge_cancels:
  assumes "a < b" "b < d" "c < e"
  shows "green_rectangular_edge_coefficient
    {(Complex a c, Complex b e), (Complex b c, Complex d e)}
    (Vertical c e b) = 0"
  using assms
  by (simp add: green_rectangular_edge_coefficient_def
    green_rectangle_edge_coefficient_def)

lemma green_shared_horizontal_edge_cancels:
  assumes "a < b" "c < d" "d < e"
  shows "green_rectangular_edge_coefficient
    {(Complex a c, Complex b d), (Complex a d, Complex b e)}
    (Horizontal a b d) = 0"
  using assms
  by (simp add: green_rectangular_edge_coefficient_def
    green_rectangle_edge_coefficient_def)

definition green_rectangle_boundary_integral ::
    "(real \<times> real \<Rightarrow> real) \<Rightarrow> (real \<times> real \<Rightarrow> real) \<Rightarrow>
      green_rectangle \<Rightarrow> real" where
  "green_rectangle_boundary_integral P Q r =
    (LINT x:{Re (fst r)..Re (snd r)}|lborel. P (x,Im (fst r))) +
    (LINT y:{Im (fst r)..Im (snd r)}|lborel. Q (Re (snd r),y)) -
    (LINT x:{Re (fst r)..Re (snd r)}|lborel. P (x,Im (snd r))) -
    (LINT y:{Im (fst r)..Im (snd r)}|lborel. Q (Re (fst r),y))"

lemma green_rectangle_edge_sum:
  assumes "green_rectangle_edges r \<subseteq> E" "finite E"
  shows "(\<Sum>e\<in>E. of_int (green_rectangle_edge_coefficient r e) *
      green_edge_integral P Q e) = green_rectangle_boundary_integral P Q r"
  using assms
  by (simp add: green_rectangle_edges_def green_rectangle_edge_coefficient_def
    green_rectangle_boundary_integral_def sum.distrib sum_subtractf
    algebra_simps green_sum_single_edge)

lemma green_rectangular_boundary_sum:
  assumes "finite R"
  shows "green_rectangular_boundary_integral P Q R =
    (\<Sum>r\<in>R. green_rectangle_boundary_integral P Q r)"
proof -
  let ?E = "green_rectangular_edges R"
  have finE: "finite ?E"
    using assms by (auto simp: green_rectangular_edges_def green_rectangle_edges_def)
  have edge_sub: "green_rectangle_edges r \<subseteq> ?E" if "r \<in> R" for r
    using that by (auto simp: green_rectangular_edges_def)
  have "green_rectangular_boundary_integral P Q R =
      (\<Sum>e\<in>?E. \<Sum>r\<in>R.
        of_int (green_rectangle_edge_coefficient r e) * green_edge_integral P Q e)"
    by (simp add: green_rectangular_boundary_integral_def
      green_rectangular_edge_coefficient_def sum_distrib_right)
  also have "\<dots> = (\<Sum>r\<in>R. \<Sum>e\<in>?E.
      of_int (green_rectangle_edge_coefficient r e) * green_edge_integral P Q e)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>r\<in>R. green_rectangle_boundary_integral P Q r)"
    by (rule sum.cong[OF refl]) (use edge_sub finE in \<open>auto intro: green_rectangle_edge_sum\<close>)
  finally show ?thesis .
qed

lemma green_rectangular_ae_disjoint:
  assumes "green_rectangular_division R" "r \<in> R" "s \<in> R"
  shows "AE p in lborel.
    (p \<in> green_rectangle_set r \<and> p \<in> green_rectangle_set s) \<longrightarrow> r = s"
proof (cases "r = s")
  case True
  then show ?thesis by simp
next
  case False
  have disj: "green_rectangle_open r \<inter> green_rectangle_open s = {}"
    using assms False by (auto simp: green_rectangular_division_def)
  have null_r: "green_rectangle_set r - green_rectangle_open r \<in> null_sets lborel"
    by (simp add: green_rectangle_set_def green_rectangle_open_def
      null_sets_cbox_Diff_box)
  have null_s: "green_rectangle_set s - green_rectangle_open s \<in> null_sets lborel"
    by (simp add: green_rectangle_set_def green_rectangle_open_def
      null_sets_cbox_Diff_box)
  have sub: "green_rectangle_set r \<inter> green_rectangle_set s \<subseteq>
      (green_rectangle_set r - green_rectangle_open r) \<union>
      (green_rectangle_set s - green_rectangle_open s)"
    using disj by blast
  have "AE p in lborel. p \<notin> green_rectangle_set r \<inter> green_rectangle_set s"
    using AE_not_in[OF null_r] AE_not_in[OF null_s] sub by auto
  then show ?thesis using False by simp
qed

theorem Green_rectangular_union:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_C1 P Q R"
  shows "(LINT p:green_rectangular_region R|lborel.
      frechet_derivative Q (at p) (1,0) -
      frechet_derivative P (at p) (0,1)) =
    green_rectangular_boundary_integral P Q R"
proof -
  let ?curl = "\<lambda>p. frechet_derivative Q (at p) (1,0) -
    frechet_derivative P (at p) (0,1)"
  obtain U where RU: "green_rectangular_region R \<subseteq> U"
    and PC1: "Ck_on 1 P U" and QC1: "Ck_on 1 Q U"
    using C1 by (auto simp: green_rectangular_C1_def)
  have fin: "finite R" using div by (simp add: green_rectangular_division_def)
  have curl_cont_U: "continuous_on U ?curl"
    using PC1 QC1
    by (auto intro!: continuous_intros
      simp: One_nat_def Ck_on_Suc_iff Ck_on_0_iff)
  have cell_subset: "green_rectangle_set r \<subseteq> U" if "r \<in> R" for r
    using RU that by (auto simp: green_rectangular_region_def)
  have int_cell: "set_integrable lborel (green_rectangle_set r) ?curl"
    if "r \<in> R" for r
    unfolding set_integrable_def
    by (rule borel_integrable_compact)
      (use cell_subset[OF that] curl_cont_U in
        \<open>auto simp: green_rectangle_set_def intro: continuous_on_subset\<close>)
  have cell_C1: "green_rectangle_C1 P Q
      (Re (fst r)) (Re (snd r)) (Im (fst r)) (Im (snd r))"
    if "r \<in> R" for r
    using cell_subset[OF that] PC1 QC1
    by (auto simp: green_rectangle_C1_def green_rectangle_set_def cbox_Pair_eq)
  have valid: "Re (fst r) \<le> Re (snd r)" "Im (fst r) \<le> Im (snd r)"
    if "r \<in> R" for r
    using div that by (auto simp: green_rectangular_division_def)
  have each: "(LINT p:green_rectangle_set r|lborel. ?curl p) =
      green_rectangle_boundary_integral P Q r"
    if "r \<in> R" for r
    using Green_rectangle_four_edges_C1[OF valid(1)[OF that] valid(2)[OF that] cell_C1[OF that]]
    by (simp add: green_rectangle_set_def cbox_Pair_eq
      green_rectangle_boundary_integral_def)
  have area: "(LINT p:green_rectangular_region R|lborel. ?curl p) =
      (\<Sum>r\<in>R. LINT p:green_rectangle_set r|lborel. ?curl p)"
    unfolding green_rectangular_region_def
  proof (rule set_integral_finite_UN_AE[OF fin])
    fix r s
    assume "r \<in> R" "s \<in> R"
    then show "AE p in lborel.
        (p \<in> green_rectangle_set r \<and> p \<in> green_rectangle_set s) \<longrightarrow> r = s"
      by (rule green_rectangular_ae_disjoint[OF div])
  next
    fix r
    assume "r \<in> R"
    then show "green_rectangle_set r \<in> sets lborel"
      by (simp add: green_rectangle_set_def)
  next
    fix r
    assume "r \<in> R"
    then show "set_integrable lborel (green_rectangle_set r) ?curl"
      by (rule int_cell)
  qed
  show ?thesis
    using area green_rectangular_boundary_sum[OF fin, of P Q]
    by (simp add: each)
qed

corollary Green_rectangular_union_uncancelled:
  fixes P Q :: "real \<times> real \<Rightarrow> real"
  assumes "green_rectangular_division R" "green_rectangular_C1 P Q R"
  shows "(LINT p:green_rectangular_region R|lborel.
      frechet_derivative Q (at p) (1,0) -
      frechet_derivative P (at p) (0,1)) =
    (\<Sum>e\<in>green_uncancelled_edges R.
      of_int (green_rectangular_edge_coefficient R e) * green_edge_integral P Q e)"
  using Green_rectangular_union[OF assms]
    green_rectangular_boundary_uncancelled[of R P Q] assms(1)
  by (simp add: green_rectangular_division_def)

end
