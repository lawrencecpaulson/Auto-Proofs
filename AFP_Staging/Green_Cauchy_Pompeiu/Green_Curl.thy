theory Green_Curl
  imports Green_Walk_Paths
begin

text \<open>For a planar vector field, curl is the derivative of its second
  component in the first coordinate minus the derivative of its first
  component in the second coordinate.\<close>
definition green_curl :: "(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow>
    real \<times> real \<Rightarrow> real" where
  "green_curl F p =
    frechet_derivative (\<lambda>x. snd (F x)) (at p) (1,0) -
    frechet_derivative (\<lambda>x. fst (F x)) (at p) (0,1)"

definition green_rectangular_vector_C1 ::
    "(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow>
      green_rectangle set \<Rightarrow> bool" where
  "green_rectangular_vector_C1 F R \<longleftrightarrow>
    (\<exists>U. green_rectangular_region R \<subseteq> U \<and> Ck_on 1 F U)"

text \<open>The real part of the complex contour integral is the circulation
  of the vector field along the path.\<close>
definition green_circulation :: "(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow>
    (real \<Rightarrow> complex) \<Rightarrow> real" where
  "green_circulation F g =
    Re (contour_integral g
      (green_contour_coefficient (\<lambda>p. fst (F p)) (\<lambda>p. snd (F p))))"

lemma green_rectangular_vector_C1_components:
  assumes "green_rectangular_vector_C1 F R"
  shows "green_rectangular_C1 (\<lambda>p. fst (F p)) (\<lambda>p. snd (F p)) R"
proof -
  obtain U where subset: "green_rectangular_region R \<subseteq> U"
    and C1: "Ck_on 1 F U"
    using assms unfolding green_rectangular_vector_C1_def by blast
  have fst: "Ck_on 1 (\<lambda>p. fst (F p)) U"
    by (rule Ck_on_bounded_linear_compose[OF bounded_linear_fst C1])
  have snd: "Ck_on 1 (\<lambda>p. snd (F p)) U"
    by (rule Ck_on_bounded_linear_compose[OF bounded_linear_snd C1])
  show ?thesis
    unfolding green_rectangular_C1_def using subset fst snd by blast
qed

theorem Green_rectangular_union_curl:
  fixes F :: "real \<times> real \<Rightarrow> real \<times> real"
  assumes div: "green_rectangular_division R"
    and C1: "green_rectangular_vector_C1 F R"
  shows "\<exists>ws.
    (\<forall>w\<in>set ws. valid_path (green_walk_path w) \<and>
      pathfinish (green_walk_path w) = pathstart (green_walk_path w)) \<and>
    mset (concat ws) = mset (green_directed_boundary R) \<and>
    (LINT p:green_rectangular_region R|lborel. green_curl F p) =
      (\<Sum>w\<leftarrow>ws. green_circulation F (green_walk_path w))"
proof -
  have components: "green_rectangular_C1
      (\<lambda>p. fst (F p)) (\<lambda>p. snd (F p)) R"
    by (rule green_rectangular_vector_C1_components[OF C1])
  obtain ws where closed: "\<forall>w\<in>set ws. valid_path (green_walk_path w) \<and>
      pathfinish (green_walk_path w) = pathstart (green_walk_path w)"
    and edges: "mset (concat ws) = mset (green_directed_boundary R)"
    and area: "(LINT p:green_rectangular_region R|lborel.
        frechet_derivative (\<lambda>x. snd (F x)) (at p) (1,0) -
        frechet_derivative (\<lambda>x. fst (F x)) (at p) (0,1)) =
      Re (\<Sum>w\<leftarrow>ws. contour_integral (green_walk_path w)
        (green_contour_coefficient
          (\<lambda>p. fst (F p)) (\<lambda>p. snd (F p))))"
    using Green_rectangular_union_polygonal_contours[OF div components]
    by blast
  have re_sum: "Re (\<Sum>w\<leftarrow>ws. contour_integral (green_walk_path w)
      (green_contour_coefficient
        (\<lambda>p. fst (F p)) (\<lambda>p. snd (F p)))) =
    (\<Sum>w\<leftarrow>ws. Re (contour_integral (green_walk_path w)
      (green_contour_coefficient
        (\<lambda>p. fst (F p)) (\<lambda>p. snd (F p)))))"
    by (induction ws) simp_all
  show ?thesis
    by (intro exI[where x=ws])
      (use closed edges area re_sum in
        \<open>auto simp: green_curl_def green_circulation_def\<close>)
qed

end
