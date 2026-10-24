theory Roth_Univariate_Bridge
  imports Roth_Primitive_Height Polynomials.MPoly_Type_Univariate
begin

section \<open>The one-variable polynomial representations\<close>

lemma roth_weight_one:
  fixes r :: "nat \<Rightarrow> nat"
  shows "roth_weight 1 r I =
    real (Poly_Mapping.lookup I 0) / real (r 0)"
  by (simp add: roth_weight_def)

lemma roth_mpoly_to_poly_cast:
  fixes U :: "int mpoly"
  shows "mpoly_to_poly v
    (replace_coeff of_int U :: rat mpoly) =
    map_poly of_int (mpoly_to_poly v U)"
  by (simp add: poly_eq_iff roth_coeff_cast coeff_map_poly)

lemma roth_mpoly_to_poly_smult:
  fixes U :: "rat mpoly"
  shows "mpoly_to_poly v (MPoly_Type.smult c U) =
    Polynomial.smult c (mpoly_to_poly v U)"
  by (simp add: poly_eq_iff roth_coeff_smult_rat coeff_smult)

lemma roth_vars_poly_to_mpoly:
  fixes Q :: "'a::comm_ring_1 poly"
  shows "vars (poly_to_mpoly v Q) \<subseteq> {v}"
proof
  fix x
  assume x: "x \<in> vars (poly_to_mpoly v Q)"
  then obtain I where
    ik: "I \<in> Poly_Mapping.keys
      (mapping_of (poly_to_mpoly v Q))"
    and xk: "x \<in> Poly_Mapping.keys I"
    by (auto simp: vars_def)
  have h: "Poly_Mapping.lookup
    (mapping_of (poly_to_mpoly v Q)) I =
    (coeff Q (Poly_Mapping.lookup I v) when
      Poly_Mapping.keys I \<subseteq> {v})"
    unfolding poly_to_mpoly_def
    by (simp add: MPoly_inverse
      lookup_Abs_poly_mapping[OF poly_to_mpoly_finite])
  have sub: "Poly_Mapping.keys I \<subseteq> {v}"
    using ik h
    by (auto simp: in_keys_iff when_def split: if_splits)
  show "x \<in> {v}" using sub xk by auto
qed

lemma roth_coeffs_poly_to_mpoly:
  fixes Q :: "int poly"
  shows "MPoly_Type.coeffs (poly_to_mpoly v Q) =
    set (Polynomial.coeffs Q) - {0}"
proof (rule equalityI)
  show "MPoly_Type.coeffs (poly_to_mpoly v Q) \<subseteq>
    set (Polynomial.coeffs Q) - {0}"
  proof
    fix x
    assume x: "x \<in> MPoly_Type.coeffs (poly_to_mpoly v Q)"
    then obtain I where
      ik: "I \<in> Poly_Mapping.keys
        (mapping_of (poly_to_mpoly v Q))"
      and xeq: "x = MPoly_Type.coeff (poly_to_mpoly v Q) I"
      by (auto simp: roth_coeffs_eq)
    have sub: "Poly_Mapping.keys I \<subseteq> {v}"
      using ik roth_vars_poly_to_mpoly[of v Q]
      by (auto simp: vars_def)
    have xeq2: "x = Polynomial.coeff Q
      (Poly_Mapping.lookup I v)"
      using xeq sub
      unfolding MPoly_Type.coeff_def poly_to_mpoly_def
      by (simp add: MPoly_inverse
        lookup_Abs_poly_mapping[OF poly_to_mpoly_finite])
    have xnz: "x \<noteq> 0" using ik xeq
      by (simp add: MPoly_Type.coeff_def in_keys_iff)
    show "x \<in> set (Polynomial.coeffs Q) - {0}"
      using xeq2 xnz range_coeff[of Q] by auto
  qed
  show "set (Polynomial.coeffs Q) - {0} \<subseteq>
    MPoly_Type.coeffs (poly_to_mpoly v Q)"
  proof
    fix x
    assume x: "x \<in> set (Polynomial.coeffs Q) - {0}"
    obtain k where xeq: "x = Polynomial.coeff Q k"
      using x range_coeff[of Q] by auto
    have xnz: "x \<noteq> 0" using x by auto
    have h: "MPoly_Type.coeff (poly_to_mpoly v Q)
      (Poly_Mapping.single v k) = x"
      using xeq by (simp add: coeff_poly_to_mpoly)
    have ik: "Poly_Mapping.single v k \<in>
      Poly_Mapping.keys (mapping_of (poly_to_mpoly v Q))"
      using h xnz
      by (simp add: MPoly_Type.coeff_def in_keys_iff)
    show "x \<in> MPoly_Type.coeffs (poly_to_mpoly v Q)"
      using ik h by (auto simp: roth_coeffs_eq)
  qed
qed

lemma roth_Gcd_remove_zero_int:
  fixes A :: "int set"
  shows "Gcd (A - {0}) = Gcd A"
proof (cases "0 \<in> A")
  case True
  have eq: "A = insert 0 (A - {0})" using True by auto
  have h0: "Gcd A = Gcd (insert 0 (A - {0}))"
    using eq by (rule arg_cong)
  have h1: "Gcd (insert 0 (A - {0})) = Gcd (A - {0})"
    by (simp only: Gcd_insert gcd_0_left normalize_Gcd)
  show ?thesis using h0 h1 by simp
next
  case False
  then show ?thesis by simp
qed

lemma roth_content_poly_to_mpoly:
  fixes Q :: "int poly"
  shows "Gcd (MPoly_Type.coeffs (poly_to_mpoly v Q)) =
    Polynomial.content Q"
  by (simp add: roth_coeffs_poly_to_mpoly
    roth_Gcd_remove_zero_int Polynomial.content_def)

lemma roth_primitive_poly_to_mpoly:
  fixes Q :: "int poly"
  shows "MPoly_Type.primitive (poly_to_mpoly v Q) \<longleftrightarrow>
    Polynomial.content Q = 1"
  by (simp add: MPoly_Type.primitive_def
    roth_content_poly_to_mpoly)

lemma roth_coeffs_mpoly_to_poly:
  fixes U :: "int mpoly"
  assumes uv: "vars U \<subseteq> {v}"
  shows "set (Polynomial.coeffs (mpoly_to_poly v U)) - {0} =
    MPoly_Type.coeffs U"
  using roth_coeffs_poly_to_mpoly[of v "mpoly_to_poly v U"]
    mpoly_to_poly_inverse[OF uv] by simp

lemma roth_content_mpoly_to_poly:
  fixes U :: "int mpoly"
  assumes uv: "vars U \<subseteq> {v}"
  shows "Polynomial.content (mpoly_to_poly v U) =
    Gcd (MPoly_Type.coeffs U)"
  using roth_content_poly_to_mpoly[of v "mpoly_to_poly v U"]
    mpoly_to_poly_inverse[OF uv] by simp

lemma roth_primitive_mpoly_to_poly:
  fixes U :: "int mpoly"
  assumes uv: "vars U \<subseteq> {v}"
  shows "Polynomial.content (mpoly_to_poly v U) = 1
    \<longleftrightarrow> MPoly_Type.primitive U"
  by (simp add: roth_content_mpoly_to_poly[OF uv]
    MPoly_Type.primitive_def)

lemma roth_int_coeff_sup_poly_coeff:
  fixes Q :: "int poly"
  shows "nat (abs (Polynomial.coeff Q k)) \<le>
    roth_int_coeff_sup (poly_to_mpoly v Q)"
  using roth_int_coeff_sup_coeff
    [of "poly_to_mpoly v Q" "Poly_Mapping.single v k"]
  by (simp add: coeff_poly_to_mpoly)

lemma roth_int_coeff_sup_poly_coeffs:
  fixes Q :: "int poly"
  assumes c: "c \<in> set (Polynomial.coeffs Q)"
  shows "nat (abs c) \<le> roth_int_coeff_sup (poly_to_mpoly v Q)"
proof -
  obtain k where "c = Polynomial.coeff Q k"
    using c range_coeff[of Q] by auto
  then show ?thesis
    using roth_int_coeff_sup_poly_coeff[of Q k v] by simp
qed

lemma roth_poly_to_mpoly_nonzero:
  fixes Q :: "'a::comm_ring_1 poly"
  assumes "Q \<noteq> 0"
  shows "poly_to_mpoly v Q \<noteq> 0"
  using assms poly_to_mpoly_inverse[of v Q]
    poly_to_mpoly_inverse[of v 0] poly_to_mpoly0[of v]
  by metis

lemma roth_mpoly_to_poly_nonzero:
  fixes U :: "'a::comm_ring_1 mpoly"
  assumes u: "U \<noteq> 0" and uv: "vars U \<subseteq> {v}"
  shows "mpoly_to_poly v U \<noteq> 0"
  using u mpoly_to_poly_inverse[OF uv] poly_to_mpoly0
  by metis

lemma roth_proj_height_poly_to_mpoly:
  fixes Q :: "int poly"
  assumes q: "Q \<noteq> 0" and prim: "Polynomial.content Q = 1"
  shows "roth_proj_height
    (replace_coeff of_int (poly_to_mpoly v Q) :: rat mpoly) =
    roth_int_coeff_sup (poly_to_mpoly v Q)"
  by (rule roth_proj_height_cast_primitive
    [OF roth_poly_to_mpoly_nonzero[OF q]])
    (simp add: roth_primitive_poly_to_mpoly prim)

end
