theory Row_Vector
  imports Row_Independence
begin

text \<open>Green, Section 3, Lemma 3.1: a linear relation between the
  derivative rows is encoded as a bivariate coefficient polynomial.\<close>

definition green_monom_index :: "nat \<times> nat \<Rightarrow> nat \<Rightarrow>\<^sub>0 nat" where
  "green_monom_index k =
    Poly_Mapping.single 0 (fst k) + Poly_Mapping.single 1 (snd k)"

lemma green_monom_index_first [simp]:
  "Poly_Mapping.lookup (green_monom_index k) 0 = fst k"
  by (simp add: green_monom_index_def Poly_Mapping.lookup_add
    Poly_Mapping.lookup_single)

lemma green_monom_index_second [simp]:
  "Poly_Mapping.lookup (green_monom_index k) 1 = snd k"
  by (simp add: green_monom_index_def Poly_Mapping.lookup_add
    Poly_Mapping.lookup_single)

lemma green_monom_index_inj: "inj green_monom_index"
  by (rule injI) (metis green_monom_index_first
    green_monom_index_second prod.expand)

definition green_row_polynomial ::
    "(nat \<times> nat) set \<Rightarrow> (nat \<times> nat \<Rightarrow> complex) \<Rightarrow> complex mpoly" where
  "green_row_polynomial K c =
    (\<Sum>k\<in>K. MPoly_Type.monom (green_monom_index k) (c k))"

lemma green_row_polynomial_coefficient:
  assumes finite: "finite K"
  shows "MPoly_Type.coeff (green_row_polynomial K c) (green_monom_index k) =
    (if k \<in> K then c k else 0)"
proof -
  have "MPoly_Type.coeff (green_row_polynomial K c) (green_monom_index k) =
      (\<Sum>t\<in>K. if green_monom_index t = green_monom_index k then c t else 0)"
    by (simp add: green_row_polynomial_def coeff_sum[OF finite] coeff_monom)
  also have "... = (\<Sum>t\<in>K. if t = k then c t else 0)"
  proof -
    have "green_monom_index t = green_monom_index k \<longleftrightarrow> t = k"
      for t
      using green_monom_index_inj by (auto dest: injD)
    then show ?thesis by simp
  qed
  also have "... = (if k \<in> K then c k else 0)"
    using finite by simp
  finally show ?thesis .
qed

lemma green_monom_index_keys:
  "Poly_Mapping.keys (green_monom_index k) \<subseteq> {0,1}"
proof -
  have "Poly_Mapping.keys (green_monom_index k) \<subseteq>
      Poly_Mapping.keys (Poly_Mapping.single 0 (fst k)) \<union>
      Poly_Mapping.keys (Poly_Mapping.single 1 (snd k))"
    unfolding green_monom_index_def by (rule Poly_Mapping.keys_add)
  also have "... \<subseteq> {0,1}" by auto
  finally show ?thesis .
qed

lemma green_row_polynomial_bivariate:
  assumes finite: "finite K"
  shows "bivariate (green_row_polynomial K c)"
proof -
  have mono: "vars (MPoly_Type.monom (green_monom_index k) (c k)) \<subseteq> {0,1}"
    for k
    using vars_monom_subset[of "green_monom_index k" "c k"]
      green_monom_index_keys[of k] by blast
  have "vars (green_row_polynomial K c) \<subseteq>
      (\<Union>k\<in>K. vars (MPoly_Type.monom (green_monom_index k) (c k)))"
    unfolding green_row_polynomial_def
    by (rule vars_setsum[OF finite])
  then have "vars (green_row_polynomial K c) \<subseteq> {0,1}"
    using mono by blast
  then show ?thesis by (simp add: bivariate_def)
qed

lemma green_monom_degree_le:
  "MPoly_Type.degree (MPoly_Type.monom m (c::complex)) v \<le>
    Poly_Mapping.lookup m v"
  by (simp add: MPoly_Type.degree.rep_eq)

lemma green_row_polynomial_degree_le:
  assumes finite: "finite K"
    and bound: "\<And>k. k \<in> K \<Longrightarrow>
      Poly_Mapping.lookup (green_monom_index k) v \<le> D"
  shows "MPoly_Type.degree (green_row_polynomial K c) v \<le> D"
proof -
  have point: "MPoly_Type.degree
      (MPoly_Type.monom (green_monom_index k) (c k)) v \<le> D"
    if "k \<in> K" for k
    using green_monom_degree_le[of "green_monom_index k" "c k" v]
      bound[OF that] by linarith
  have "MPoly_Type.degree (green_row_polynomial K c) v \<le>
    Max (insert 0 ((\<lambda>k. MPoly_Type.degree
      (MPoly_Type.monom (green_monom_index k) (c k)) v) ` K))"
    unfolding green_row_polynomial_def by (rule degree_sum[OF finite])
  also have "... \<le> D"
    by (rule Max.boundedI) (use finite point in auto)
  finally show ?thesis .
qed

lemma green_first_derivative_specialize:
  "green_first_derivative j F z =
    poly ((pderiv ^^ j) (specialize_second (snd z) F)) (fst z)"
  by (simp add: green_first_derivative_def specialize_first_higher_pderiv)

lemma specialize_second_sum:
  "specialize_second a (\<Sum>k\<in>K. F k) =
    (\<Sum>k\<in>K. specialize_second a (F k))"
proof (rule poly_ext)
  fix x
  show "poly (specialize_second a (\<Sum>k\<in>K. F k)) x =
      poly (\<Sum>k\<in>K. specialize_second a (F k)) x"
    by (induction K rule: infinite_finite_induct)
      (simp_all add: poly_specialize_second insertion_add)
qed

lemma green_first_derivative_sum:
  "green_first_derivative j (\<Sum>k\<in>K. F k) z =
    (\<Sum>k\<in>K. green_first_derivative j (F k) z)"
  by (simp add: green_first_derivative_specialize specialize_second_sum
    higher_pderiv_sum poly_sum)

lemma green_first_derivative_const_mult:
  "green_first_derivative j (Const c * F) z =
    c * green_first_derivative j F z"
proof -
  have "specialize_second (snd z) (Const c * F) =
      Polynomial.smult c (specialize_second (snd z) F)"
    by (rule poly_ext) (simp add: poly_specialize_second insertion_mult)
  then show ?thesis
    by (simp add: green_first_derivative_specialize higher_pderiv_smult)
qed

lemma green_monom_scalar:
  "MPoly_Type.monom m (c::complex) =
    Const c * MPoly_Type.monom m 1"
proof -
  have "Const c = MPoly_Type.monom 0 c"
    by (simp add: Const.abs_eq Const\<^sub>0_def MPoly_Type.monom.abs_eq)
  then show ?thesis
    by (simp add: MPoly_Type.mult_monom)
qed

lemma green_row_polynomial_derivative:
  "green_first_derivative j (green_row_polynomial K c) z =
    (\<Sum>k\<in>K. c k *
      green_first_derivative j (MPoly_Type.monom (green_monom_index k) 1) z)"
proof -
  have "green_first_derivative j (green_row_polynomial K c) z =
      (\<Sum>k\<in>K. green_first_derivative j
        (MPoly_Type.monom (green_monom_index k) (c k)) z)"
    unfolding green_row_polynomial_def by (rule green_first_derivative_sum)
  also have "... = (\<Sum>k\<in>K. c k *
      green_first_derivative j (MPoly_Type.monom (green_monom_index k) 1) z)"
  proof (rule sum.cong)
    show "K = K" by simp
    fix k assume "k \<in> K"
    have eq: "MPoly_Type.monom (green_monom_index k) (c k) =
        Const (c k) * MPoly_Type.monom (green_monom_index k) 1"
      by (rule green_monom_scalar)
    show "green_first_derivative j
      (MPoly_Type.monom (green_monom_index k) (c k)) z =
      c k * green_first_derivative j
      (MPoly_Type.monom (green_monom_index k) 1) z"
      by (subst eq) (rule green_first_derivative_const_mult)
  qed
  finally show ?thesis .
qed

definition green_row_indices :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
  "green_row_indices R S = {..<R} \<times> {..<S}"

definition green_row_relation ::
    "(complex \<times> complex) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      (nat \<times> nat \<Rightarrow> complex) \<Rightarrow> bool" where
  "green_row_relation P J R S c \<longleftrightarrow>
    (\<forall>z\<in>P. \<forall>j<J.
      (\<Sum>k\<in>green_row_indices R S. c k *
        green_first_derivative j
          (MPoly_Type.monom (green_monom_index k) 1) z) = 0)"

lemma green_row_indices_finite [simp]: "finite (green_row_indices R S)"
  by (simp add: green_row_indices_def)

lemma green_row_polynomial_rectangle_degree:
  "MPoly_Type.degree (green_row_polynomial (green_row_indices R S) c) 0 \<le> R"
  "MPoly_Type.degree (green_row_polynomial (green_row_indices R S) c) 1 \<le> S"
proof -
  have finite: "finite (green_row_indices R S)" by simp
  have first: "Poly_Mapping.lookup (green_monom_index k) 0 \<le> R"
    if "k \<in> green_row_indices R S" for k
    using that by (auto simp: green_row_indices_def)
  have second: "Poly_Mapping.lookup (green_monom_index k) 1 \<le> S"
    if "k \<in> green_row_indices R S" for k
  proof -
    have "Poly_Mapping.lookup (green_monom_index k) 1 = snd k"
      by (rule green_monom_index_second)
    moreover have "snd k < S"
      using that by (auto simp: green_row_indices_def)
    ultimately show ?thesis by simp
  qed
  show "MPoly_Type.degree (green_row_polynomial (green_row_indices R S) c) 0 \<le> R"
    by (rule green_row_polynomial_degree_le[OF finite first])
  show "MPoly_Type.degree (green_row_polynomial (green_row_indices R S) c) 1 \<le> S"
    by (rule green_row_polynomial_degree_le[OF finite second])
qed

lemma (in green_point_configuration) green_rows_independent:
  assumes dimension: "J * card I > 2 * R * S + J * (R + S)"
    and relation: "green_row_relation (point ` I) J R S c"
  shows "\<And>k. k \<in> green_row_indices R S \<Longrightarrow> c k = 0"
proof -
  let ?K = "green_row_indices R S"
  let ?F = "green_row_polynomial ?K c"
  have bv: "bivariate ?F"
    by (rule green_row_polynomial_bivariate) simp
  have degree_first: "MPoly_Type.degree ?F 0 \<le> R"
    and degree_second: "MPoly_Type.degree ?F 1 \<le> S"
    by (rule green_row_polynomial_rectangle_degree)+
  have vanishing: "green_first_derivative j ?F (point i) = 0"
    if "i \<in> I" and "j < J" for i j
    using relation that
    by (simp add: green_row_relation_def green_row_polynomial_derivative)
  have zero: "?F = 0"
    by (rule no_vanishing_polynomial[OF dimension bv degree_first degree_second
      vanishing])
  fix k assume "k \<in> ?K"
  have "MPoly_Type.coeff ?F (green_monom_index k) = c k"
    using \<open>k \<in> ?K\<close> by (simp add: green_row_polynomial_coefficient)
  with zero show "c k = 0" by simp
qed

end
