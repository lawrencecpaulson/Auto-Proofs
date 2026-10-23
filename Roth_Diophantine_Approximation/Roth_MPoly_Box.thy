theory Roth_MPoly_Box
  imports
    "Polynomials.More_MPoly_Type"
    "HOL-Library.FuncSet"
begin

section \<open>Finite boxes of multivariate exponents\<close>

definition roth_exponent_box ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) set" where
  "roth_exponent_box m r =
    (\<lambda>f. Abs_poly_mapping (\<lambda>v. if v < m then f v else 0)) `
      (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"

lemma finite_roth_exponent_box [simp]:
  "finite (roth_exponent_box m r)"
  unfolding roth_exponent_box_def by (intro finite_imageI finite_PiE) auto

lemma roth_exponent_boxI:
  assumes vars: "Poly_Mapping.keys I \<subseteq> {..<m}"
    and bound: "\<And>v. v < m \<Longrightarrow> Poly_Mapping.lookup I v \<le> r v"
  shows "I \<in> roth_exponent_box m r"
proof -
  let ?f = "restrict (Poly_Mapping.lookup I) {..<m}"
  have fmem: "?f \<in> (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
    using bound by (auto simp: PiE_def)
  have fin: "finite {v. (if v < m then ?f v else 0) \<noteq> 0}"
    by (rule finite_subset[of _ "{..<m}"]) auto
  have "Abs_poly_mapping (\<lambda>v. if v < m then ?f v else 0) = I"
  proof (rule Poly_Mapping.poly_mapping_eqI)
    fix v
    show "Poly_Mapping.lookup
        (Abs_poly_mapping (\<lambda>v. if v < m then ?f v else 0)) v =
        Poly_Mapping.lookup I v"
    proof (cases "v < m")
      case True
      then show ?thesis
        using fin by simp
    next
      case False
      then have "v \<notin> Poly_Mapping.keys I"
        using vars by auto
      then show ?thesis
        using fin False by (simp add: not_in_keys_iff_lookup_eq_zero)
    qed
  qed
  then have eq: "I = Abs_poly_mapping (\<lambda>v. if v < m then ?f v else 0)"
    by simp
  show ?thesis
    unfolding roth_exponent_box_def
  proof (rule image_eqI[where x = ?f])
    show "I = Abs_poly_mapping (\<lambda>v. if v < m then ?f v else 0)"
      by (rule eq)
    show "?f \<in> (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
      by (rule fmem)
  qed
qed

lemma roth_exponent_boxD:
  assumes "I \<in> roth_exponent_box m r"
  shows "Poly_Mapping.keys I \<subseteq> {..<m}"
    "\<And>v. v < m \<Longrightarrow> Poly_Mapping.lookup I v \<le> r v"
proof -
  obtain f where f:
    "f \<in> (\<Pi>\<^sub>E v \<in> {..<m}. {..r v})"
    "I = Abs_poly_mapping (\<lambda>v. if v < m then f v else 0)"
    using assms by (auto simp: roth_exponent_box_def)
  have fin: "finite {v. (if v < m then f v else 0) \<noteq> 0}"
    by (rule finite_subset[of _ "{..<m}"]) auto
  show "Poly_Mapping.keys I \<subseteq> {..<m}"
    using f fin by (auto simp: Poly_Mapping.keys.rep_eq)
  show "\<And>v. v < m \<Longrightarrow> Poly_Mapping.lookup I v \<le> r v"
    using f fin by (auto simp: PiE_def)
qed

lemma roth_exponent_box_iff:
  "I \<in> roth_exponent_box m r \<longleftrightarrow>
    Poly_Mapping.keys I \<subseteq> {..<m} \<and>
    (\<forall>v<m. Poly_Mapping.lookup I v \<le> r v)"
  using roth_exponent_boxI roth_exponent_boxD by blast

definition roth_poly_in_box ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a::zero mpoly \<Rightarrow> bool" where
  "roth_poly_in_box m r P \<longleftrightarrow>
    Poly_Mapping.keys (mapping_of P) \<subseteq> roth_exponent_box m r"

lemma roth_poly_in_box_zero [simp]:
  "roth_poly_in_box m r (0::'a::zero mpoly)"
  by (simp add: roth_poly_in_box_def zero_mpoly.rep_eq)

lemma roth_poly_in_box_monom:
  assumes "I \<in> roth_exponent_box m r"
  shows "roth_poly_in_box m r (monom I c)"
  using assms
  by (auto simp: roth_poly_in_box_def mapping_of_monom keys_single)

lemma roth_poly_in_box_add:
  assumes "roth_poly_in_box m r P" "roth_poly_in_box m r Q"
  shows "roth_poly_in_box m r (P + Q)"
  using assms
  by (auto simp: roth_poly_in_box_def plus_mpoly.rep_eq
    dest: subsetD[OF Poly_Mapping.keys_add])

lemma roth_poly_in_box_sum:
  assumes "finite S" "\<And>x. x \<in> S \<Longrightarrow> roth_poly_in_box m r (P x)"
  shows "roth_poly_in_box m r (\<Sum>x\<in>S. P x)"
  using assms by (induction S rule: finite_induct)
    (simp_all add: roth_poly_in_box_add)

lemma roth_coeff_zero_outside_box:
  assumes "roth_poly_in_box m r P" "I \<notin> roth_exponent_box m r"
  shows "coeff P I = 0"
  using assms by (auto simp: roth_poly_in_box_def coeff_def
    not_in_keys_iff_lookup_eq_zero)

lemma roth_exponent_le_degree:
  fixes P :: "'a::zero mpoly"
  assumes "I \<in> Poly_Mapping.keys (mapping_of P)"
  shows "Poly_Mapping.lookup I v \<le> MPoly_Type.degree P v"
  using assms by (simp add: MPoly_Type.degree.rep_eq)

lemma roth_degree_le_of_box:
  fixes P :: "'a::zero mpoly"
  assumes "roth_poly_in_box m r P" "v < m"
  shows "MPoly_Type.degree P v \<le> r v"
  using assms unfolding roth_poly_in_box_def MPoly_Type.degree.rep_eq
  by (auto simp: Max_le_iff roth_exponent_box_iff)

lemma roth_degree_outside_box:
  fixes P :: "'a::zero mpoly"
  assumes box: "roth_poly_in_box m r P" and outside: "m \<le> v"
  shows "MPoly_Type.degree P v = 0"
proof -
  have all_zero: "Poly_Mapping.lookup I v = 0"
    if "I \<in> Poly_Mapping.keys (mapping_of P)" for I
  proof -
    have "I \<in> roth_exponent_box m r"
      using box that by (auto simp: roth_poly_in_box_def)
    then have "Poly_Mapping.keys I \<subseteq> {..<m}"
      by (rule roth_exponent_boxD(1))
    then have "v \<notin> Poly_Mapping.keys I"
      using outside by auto
    then show ?thesis
      by (simp add: not_in_keys_iff_lookup_eq_zero)
  qed
  have set_eq: "insert 0 ((\<lambda>I. Poly_Mapping.lookup I v) `
      Poly_Mapping.keys (mapping_of P)) = {0}"
    using all_zero by auto
  have "MPoly_Type.degree P v = Max {0}"
    by (simp only: MPoly_Type.degree.rep_eq set_eq)
  then show ?thesis
    by simp
qed

lemma roth_poly_in_box_iff_degree:
  fixes P :: "'a::zero mpoly"
  shows "roth_poly_in_box m r P \<longleftrightarrow>
    (\<forall>v<m. MPoly_Type.degree P v \<le> r v) \<and>
    (\<forall>v\<ge>m. MPoly_Type.degree P v = 0)"
proof
  assume "roth_poly_in_box m r P"
  then show "(\<forall>v<m. MPoly_Type.degree P v \<le> r v) \<and>
    (\<forall>v\<ge>m. MPoly_Type.degree P v = 0)"
    using roth_degree_le_of_box roth_degree_outside_box by blast
next
  assume degrees: "(\<forall>v<m. MPoly_Type.degree P v \<le> r v) \<and>
    (\<forall>v\<ge>m. MPoly_Type.degree P v = 0)"
  have in_box: "I \<in> roth_exponent_box m r"
    if I: "I \<in> Poly_Mapping.keys (mapping_of P)" for I
  proof (rule roth_exponent_boxI)
    show "Poly_Mapping.keys I \<subseteq> {..<m}"
    proof
      fix v
      assume v: "v \<in> Poly_Mapping.keys I"
      show "v \<in> {..<m}"
      proof (rule ccontr)
        assume "v \<notin> {..<m}"
        then have "MPoly_Type.degree P v = 0"
          using degrees by simp
        then have "Poly_Mapping.lookup I v = 0"
          using roth_exponent_le_degree[OF I, where v = v] by simp
        then have "v \<notin> Poly_Mapping.keys I"
          by (rule lookup_eq_zero_in_keys_contradict)
        then show False
          using v by simp
      qed
    qed
    fix v
    assume v: "v < m"
    have "Poly_Mapping.lookup I v \<le> MPoly_Type.degree P v"
      by (rule roth_exponent_le_degree[OF I])
    also have "\<dots> \<le> r v"
      using degrees v by simp
    finally show "Poly_Mapping.lookup I v \<le> r v" .
  qed
  show "roth_poly_in_box m r P"
    using in_box by (auto simp: roth_poly_in_box_def)
qed

end
