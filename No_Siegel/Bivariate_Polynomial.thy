theory Bivariate_Polynomial
  imports Finite_Grid Factor_Algebraic_Polynomial.Poly_Connection
begin

text \<open>Green, Section 3 ("The Gram matrix is nonsingular"), proof of
  Lemma 3.1: factor a bivariate polynomial and control its specialised
  factors. We use AFP's polynomial in a distinguished variable, with
  multivariate coefficients. Specialising all other variables gives Green's
  \<open>F(z,a)\<close> when \<open>vars F \<subseteq> {0, 1}\<close>.\<close>

definition bivariate :: "complex mpoly \<Rightarrow> bool" where
  "bivariate F \<longleftrightarrow> vars F \<subseteq> {0, 1}"

lemma vars_mult_nonzero:
  fixes F G :: "complex mpoly"
  assumes "F \<noteq> 0" "G \<noteq> 0"
  shows "vars (F * G) = vars F \<union> vars G"
proof (rule set_eqI)
  fix i
  have "MPoly_Type.degree (F * G) i = MPoly_Type.degree F i + MPoly_Type.degree G i"
    using mpoly_degree_mult_eq[OF assms] .
  then show "i \<in> vars (F * G) \<longleftrightarrow> i \<in> vars F \<union> vars G"
    by (simp add: degree_pos_iff[symmetric])
qed

lemma bivariate_factors:
  fixes F G :: "complex mpoly"
  assumes "F \<noteq> 0" "G \<noteq> 0" "bivariate (F * G)"
  shows "bivariate F \<and> bivariate G"
  using assms vars_mult_nonzero[of F G]
  unfolding bivariate_def by auto

lemma nonunit_bivariate_degree_pos:
  fixes F :: "complex mpoly"
  assumes "bivariate F" "F \<noteq> 0" "\<not> F dvd 1"
  shows "0 < MPoly_Type.degree F 0 + MPoly_Type.degree F 1"
proof (rule ccontr)
  assume "\<not> 0 < MPoly_Type.degree F 0 + MPoly_Type.degree F 1"
  then have "MPoly_Type.degree F 0 = 0" "MPoly_Type.degree F 1 = 0"
    by auto
  then have "vars F = {}"
    using assms(1) unfolding bivariate_def
    by (auto simp: degree_eq_0_iff)
  then obtain c where "F = Const c" by (rule vars_emptyE) blast
  with assms(2) have "c \<noteq> 0" by auto
  then have "F dvd 1" using \<open>F = Const c\<close>
    by (auto simp: dvd_field_iff)
  with assms(3) show False by simp
qed

lemma bivariate_coeff_first:
  assumes "bivariate F"
  shows "vars (coeff (mpoly_to_mpoly_poly 0 F) k) \<subseteq> {1}"
  using assms vars_coeff_mpoly_to_mpoly_poly[of 0 F k]
  unfolding bivariate_def by auto

lemma mpoly_to_poly_zero [simp]:
  "mpoly_to_poly i (0 :: complex mpoly) = 0"
  by (rule poly_eqI) simp


lemma mpoly_to_poly_mult_pure:
  fixes A B :: "complex mpoly"
  assumes av: "vars A \<subseteq> {1}" and bv: "vars B \<subseteq> {1}"
  shows "mpoly_to_poly 1 (A * B) = mpoly_to_poly 1 A * mpoly_to_poly 1 B"
proof (rule poly_ext)
  fix x :: complex
  have cv: "vars (A * B) \<subseteq> {1}"
    using vars_mult[of A B] av bv by blast
  show "poly (mpoly_to_poly 1 (A * B)) x =
      poly (mpoly_to_poly 1 A * mpoly_to_poly 1 B) x"
    using poly_eq_insertion[OF cv, of x]
      poly_eq_insertion[OF av, of x] poly_eq_insertion[OF bv, of x]
    by (simp add: insertion_mult)
qed

definition bivariate_as_poly_poly :: "complex mpoly \<Rightarrow> complex poly poly" where
  "bivariate_as_poly_poly F =
    map_poly (mpoly_to_poly 1) (mpoly_to_mpoly_poly 0 F)"

definition poly_poly_as_bivariate :: "complex poly poly \<Rightarrow> complex mpoly" where
  "poly_poly_as_bivariate P =
    poly (map_poly (poly_to_mpoly 1) P) (Var 0)"


lemma mpoly_to_poly_sum:
  fixes f :: "'a \<Rightarrow> complex mpoly"
  assumes "finite A"
  shows "mpoly_to_poly 1 (\<Sum>a\<in>A. f a) =
    (\<Sum>a\<in>A. mpoly_to_poly 1 (f a))"
  using assms by (induction A rule: finite_induct)
    (simp_all add: mpoly_to_poly_add)

lemma bivariate_as_poly_poly_mult:
  assumes bvF: "bivariate F" and bvG: "bivariate G"
  shows "bivariate_as_poly_poly (F * G) =
    bivariate_as_poly_poly F * bivariate_as_poly_poly G"
proof (rule poly_eqI)
  fix n
  let ?p = "mpoly_to_mpoly_poly 0 F"
  let ?q = "mpoly_to_mpoly_poly 0 G"
  have cF: "vars (coeff ?p k) \<subseteq> {1}" for k
    by (rule bivariate_coeff_first[OF bvF])
  have cG: "vars (coeff ?q k) \<subseteq> {1}" for k
    by (rule bivariate_coeff_first[OF bvG])
  have "coeff (bivariate_as_poly_poly (F * G)) n =
      mpoly_to_poly 1 (coeff (?p * ?q) n)"
    by (simp add: bivariate_as_poly_poly_def coeff_map_poly)
  also have "... = (\<Sum>k\<le>n. mpoly_to_poly 1 (coeff ?p k * coeff ?q (n - k)))"
    unfolding coeff_mult by (rule mpoly_to_poly_sum) simp
  also have "... = (\<Sum>k\<le>n. mpoly_to_poly 1 (coeff ?p k) *
      mpoly_to_poly 1 (coeff ?q (n - k)))"
  proof (rule sum.cong)
    show "{..n} = {..n}" by simp
    fix k
    assume "k \<in> {..n}"
    show "mpoly_to_poly 1 (coeff ?p k * coeff ?q (n - k)) =
      mpoly_to_poly 1 (coeff ?p k) * mpoly_to_poly 1 (coeff ?q (n - k))"
      by (rule mpoly_to_poly_mult_pure[OF cF[of k] cG[of "n - k"]])
  qed
  also have "... = coeff (bivariate_as_poly_poly F * bivariate_as_poly_poly G) n"
    by (simp add: bivariate_as_poly_poly_def coeff_mult coeff_map_poly)
  finally show "coeff (bivariate_as_poly_poly (F * G)) n =
    coeff (bivariate_as_poly_poly F * bivariate_as_poly_poly G) n" .
qed

lemma poly_poly_as_bivariate_inverse:
  assumes bv: "bivariate F"
  shows "poly_poly_as_bivariate (bivariate_as_poly_poly F) = F"
proof -
  let ?p = "mpoly_to_mpoly_poly 0 F"
  have c1: "coeff (map_poly (mpoly_to_poly 1) ?p) k =
      mpoly_to_poly 1 (coeff ?p k)" for k
    by (subst coeff_map_poly[where f="mpoly_to_poly 1"]) simp_all
  have eq: "map_poly (poly_to_mpoly 1) (map_poly (mpoly_to_poly 1) ?p) = ?p"
  proof (rule poly_eqI)
    fix k
    have "coeff (map_poly (poly_to_mpoly 1) (map_poly (mpoly_to_poly 1) ?p)) k
        = poly_to_mpoly 1 (coeff (map_poly (mpoly_to_poly 1) ?p) k)"
      by (subst coeff_map_poly[where f="poly_to_mpoly 1"])
        (simp_all add: poly_to_mpoly0)
    also have "... = poly_to_mpoly 1 (mpoly_to_poly 1 (coeff ?p k))"
      by (simp only: c1)
    also have "... = coeff ?p k"
      by (rule mpoly_to_poly_inverse[OF bivariate_coeff_first[OF bv]])
    finally show "coeff (map_poly (poly_to_mpoly 1)
        (map_poly (mpoly_to_poly 1) ?p)) k = coeff ?p k" .
  qed
  show ?thesis
    using eq by (simp add: bivariate_as_poly_poly_def
      poly_poly_as_bivariate_def poly_mpoly_to_mpoly_poly)
qed

lemma bivariate_as_poly_poly_inj:
  assumes "bivariate F" "bivariate G"
    and "bivariate_as_poly_poly F = bivariate_as_poly_poly G"
  shows "F = G"
  using assms poly_poly_as_bivariate_inverse by metis

lemma bivariate_as_poly_poly_nonzero:
  assumes bv: "bivariate F" and nz: "F \<noteq> 0"
  shows "bivariate_as_poly_poly F \<noteq> 0"
proof
  assume z: "bivariate_as_poly_poly F = 0"
  have "F = poly_poly_as_bivariate 0"
    using poly_poly_as_bivariate_inverse[OF bv] z by simp
  then show False using nz
    by (simp add: poly_poly_as_bivariate_def poly_to_mpoly0)
qed

abbreviation specialize_first :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> complex mpoly \<Rightarrow> complex poly" where
  "specialize_first \<alpha> x F \<equiv> partial_insertion \<alpha> x F"

abbreviation specialize_second :: "complex \<Rightarrow> complex mpoly \<Rightarrow> complex poly" where
  "specialize_second a F \<equiv> specialize_first (\<lambda>_. a) 0 F"

lemma poly_specialize_first:
  "poly (specialize_first \<alpha> i F) x = insertion (\<alpha>(i := x)) F"
  using insertion_partial_insertion[of i \<alpha> "\<alpha>(i := x)" F] by simp

lemma poly_specialize_second:
  "poly (specialize_second a F) x =
    insertion (\<lambda>i. if i = 0 then x else a) F"
  by (simp add: poly_specialize_first fun_upd_def)

lemma specialize_first_mult:
  "specialize_first \<alpha> i (F * G) = specialize_first \<alpha> i F * specialize_first \<alpha> i G"
  by (rule poly_ext) (simp add: poly_specialize_first)

lemma specialize_first_zero [simp]: "specialize_first \<alpha> i 0 = 0"
  by (rule poly_ext) (simp add: poly_specialize_first)

lemma specialize_first_one [simp]: "specialize_first \<alpha> i 1 = 1"
  by (rule poly_ext) (simp add: poly_specialize_first)

lemma specialize_first_Const [simp]: "specialize_first \<alpha> i (Const c) = [:c:]"
  by (rule poly_ext) (simp add: poly_specialize_first)

lemma specialize_first_Var [simp]:
  "specialize_first \<alpha> i (Var j) = (if i = j then [:0, 1:] else [: \<alpha> j :])"
  by (rule poly_ext) (simp add: poly_specialize_first fun_upd_def)

lemma specialize_first_eq_zero_iff:
  "specialize_first \<alpha> i F = 0 \<longleftrightarrow>
    (\<forall>k. insertion \<alpha> (coeff (mpoly_to_mpoly_poly i F) k) = 0)"
  by (simp add: poly_eq_iff)

lemma degree_specialize_first:
  "degree (specialize_first \<alpha> i F) \<le> MPoly_Type.degree F i"
  using degree_partial_insertion_le_mpoly[of \<alpha> i F] by simp

lemma degree_specialize_first_total:
  "degree (specialize_first \<alpha> i F) \<le> total_degree F"
  using degree_specialize_first[of \<alpha> i F] degree_le_total_degree[of F i] by linarith


lemma specialize_first_nonzero_if_lead:
  assumes "insertion \<alpha> (Polynomial.lead_coeff (mpoly_to_mpoly_poly i F)) \<noteq> 0"
  shows "specialize_first \<alpha> i F \<noteq> 0"
proof -
  have "coeff (specialize_first \<alpha> i F) (MPoly_Type.degree F i) \<noteq> 0"
    using assms by simp
  then show ?thesis by auto
qed

lemma degree_specialize_first_eq:
  assumes "insertion \<alpha> (Polynomial.lead_coeff (mpoly_to_mpoly_poly i F)) \<noteq> 0"
  shows "degree (specialize_first \<alpha> i F) = MPoly_Type.degree F i"
proof -
  have top: "coeff (specialize_first \<alpha> i F) (MPoly_Type.degree F i) \<noteq> 0"
    using assms by simp
  have lower: "MPoly_Type.degree F i \<le> degree (specialize_first \<alpha> i F)"
    using top by (rule le_degree)
  show ?thesis using lower degree_specialize_first[of \<alpha> i F] by linarith
qed

lemma specialize_first_pderiv:
  "pderiv (specialize_first \<alpha> i F) =
    map_poly (insertion \<alpha>) (pderiv (mpoly_to_mpoly_poly i F))"
proof -
  interpret h: idom_hom "insertion \<alpha>"
    by (unfold_locales; simp)
  show ?thesis
    unfolding partial_insertion_def by (simp add: h.map_poly_pderiv)
qed

lemma specialize_first_higher_pderiv:
  "(pderiv ^^ n) (specialize_first \<alpha> i F) =
    map_poly (insertion \<alpha>) ((pderiv ^^ n) (mpoly_to_mpoly_poly i F))"
proof -
  interpret h: idom_hom "insertion \<alpha>"
    by (unfold_locales; simp)
  show ?thesis
    unfolding partial_insertion_def by (simp add: h.map_poly_higher_pderiv)
qed

lemma specialize_first_prod_list:
  "specialize_first \<alpha> i (prod_list Fs) = prod_list (map (specialize_first \<alpha> i) Fs)"
  by (induct Fs) (simp_all add: specialize_first_mult)

lemma order_specialize_first_mult:
  assumes "specialize_first \<alpha> i F \<noteq> 0" "specialize_first \<alpha> i G \<noteq> 0"
  shows "order x (specialize_first \<alpha> i (F * G)) =
    order x (specialize_first \<alpha> i F) + order x (specialize_first \<alpha> i G)"
  using assms by (simp add: specialize_first_mult order_mult)


lemma specialize_first_prod_list_nonzero:
  assumes "\<And>F. F \<in> set Fs \<Longrightarrow> specialize_first \<alpha> i F \<noteq> 0"
  shows "specialize_first \<alpha> i (prod_list Fs) \<noteq> 0"
  using assms by (induct Fs) (simp_all add: specialize_first_mult)

lemma order_specialize_first_prod_list:
  assumes "\<And>F. F \<in> set Fs \<Longrightarrow> specialize_first \<alpha> i F \<noteq> 0"
  shows "order x (specialize_first \<alpha> i (prod_list Fs)) =
    sum_list (map (\<lambda>F. order x (specialize_first \<alpha> i F)) Fs)"
  using assms by (induct Fs) (simp_all add: specialize_first_mult order_mult specialize_first_prod_list_nonzero)

lemma order_specialize_first_le_degree:
  assumes "specialize_first \<alpha> i F \<noteq> 0"
  shows "order x (specialize_first \<alpha> i F) \<le> MPoly_Type.degree F i"
  using assms order_degree[of "specialize_first \<alpha> i F" x]
    degree_specialize_first[of \<alpha> i F] by linarith



lemma derivatives_zero_imp_order:
  fixes p :: "complex poly"
  assumes "p \<noteq> 0" "\<forall>j<J. poly ((pderiv ^^ j) p) x = 0"
  shows "J \<le> order x p"
  using assms
proof (induct J arbitrary: p)
  case 0
  then show ?case by simp
next
  case (Suc J)
  have root: "poly p x = 0" using Suc.prems(2) by auto
  have nz: "pderiv p \<noteq> 0"
  proof
    assume "pderiv p = 0"
    then obtain c where "p = [:c:]"
      using degree0_coeffs by (auto simp: pderiv_eq_0_iff)
    with root Suc.prems(1) show False by auto
  qed
  have van: "\<forall>j<J. poly ((pderiv ^^ j) (pderiv p)) x = 0"
  proof (intro allI impI)
    fix j assume j: "j < J"
    have "poly ((pderiv ^^ Suc j) p) x = 0"
      using Suc.prems(2) j by auto
    then show "poly ((pderiv ^^ j) (pderiv p)) x = 0"
      by (simp only: funpow_Suc_right o_apply)
  qed
  have "J \<le> order x (pderiv p)" using Suc.hyps[OF nz van] .
  then show ?case using order_pderiv[OF Suc.prems(1) root] by simp
qed

lemma specialized_derivatives_zero_imp_order:
  assumes "specialize_first \<alpha> i F \<noteq> 0"
    and "\<forall>j<J. poly (map_poly (insertion \<alpha>)
      ((pderiv ^^ j) (mpoly_to_mpoly_poly i F))) x = 0"
  shows "J \<le> order x (specialize_first \<alpha> i F)"
  using derivatives_zero_imp_order[OF assms(1)] assms(2)
  by (simp add: specialize_first_higher_pderiv)


lemma prod_list_mpoly_nonzero:
  fixes Fs :: "complex mpoly list"
  assumes "\<And>F. F \<in> set Fs \<Longrightarrow> F \<noteq> 0"
  shows "prod_list Fs \<noteq> 0"
  using assms by (induct Fs) auto

lemma degree_prod_list_mpoly:
  fixes Fs :: "complex mpoly list"
  assumes "\<And>F. F \<in> set Fs \<Longrightarrow> F \<noteq> 0"
  shows "MPoly_Type.degree (prod_list Fs) i =
    sum_list (map (\<lambda>F. MPoly_Type.degree F i) Fs)"
  using assms
proof (induct Fs)
  case Nil
  then show ?case by simp
next
  case (Cons F Fs)
  have nz: "F \<noteq> 0" "prod_list Fs \<noteq> 0"
    using Cons.prems prod_list_mpoly_nonzero by auto
  have deg: "MPoly_Type.degree (prod_list Fs) i =
    sum_list (map (\<lambda>G. MPoly_Type.degree G i) Fs)"
    using Cons.hyps Cons.prems by auto
  show ?case using nz deg by (simp add: mpoly_degree_mult_eq)
qed

lemma factor_product_degree:
  fixes F F0 :: "complex mpoly"
  assumes "F = F0 * prod_list Fs" "F0 \<noteq> 0"
    and "\<And>G. G \<in> set Fs \<Longrightarrow> G \<noteq> 0"
  shows "MPoly_Type.degree F i = MPoly_Type.degree F0 i +
    sum_list (map (\<lambda>G. MPoly_Type.degree G i) Fs)"
proof -
  have "prod_list Fs \<noteq> 0" using assms(3) by (rule prod_list_mpoly_nonzero)
  then show ?thesis using assms degree_prod_list_mpoly[of Fs i]
    by (simp add: mpoly_degree_mult_eq)
qed


lemma specialize_pure_second:
  assumes "vars F \<subseteq> {1}"
  shows "specialize_second a F = [:poly (mpoly_to_poly 1 F) a:]"
proof (rule poly_ext)
  fix x
  have "poly (specialize_second a F) x =
      insertion (\<lambda>i. if i = 0 then x else a) F"
    by (rule poly_specialize_second)
  also have "... = insertion (\<lambda>_. a) F"
    by (rule insertion_irrelevant_vars) (use assms in auto)
  also have "... = poly (mpoly_to_poly 1 F) a"
    using poly_eq_insertion[OF assms] by simp
  finally show "poly (specialize_second a F) x =
      poly [:poly (mpoly_to_poly 1 F) a:] x" by simp
qed

lemma pure_second_polynomial_nonzero:
  assumes "vars F \<subseteq> {1}" "F \<noteq> 0"
  shows "mpoly_to_poly 1 F \<noteq> 0"
  using assms mpoly_to_poly_inverse[of F 1] by (auto simp: poly_to_mpoly0)


lemma degree_bivariate_as_poly_poly:
  assumes bv: "bivariate F"
  shows "degree (bivariate_as_poly_poly F) = MPoly_Type.degree F 0"
proof (cases "F = 0")
  case True
  then show ?thesis by (simp add: bivariate_as_poly_poly_def)
next
  case False
  let ?p = "mpoly_to_mpoly_poly 0 F"
  have pnz: "?p \<noteq> 0"
    using False mpoly_to_mpoly_poly_eq_iff[of 0 F 0] by simp
  have top: "coeff ?p (degree ?p) \<noteq> 0"
    using pnz leading_coeff_0_iff[of ?p] by blast
  have cnz: "mpoly_to_poly 1 (coeff ?p (degree ?p)) \<noteq> 0"
    by (rule pure_second_polynomial_nonzero
        [OF bivariate_coeff_first[OF bv] top])
  have mapc: "coeff (bivariate_as_poly_poly F) k =
      mpoly_to_poly 1 (coeff ?p k)" for k
    unfolding bivariate_as_poly_poly_def
    by (subst coeff_map_poly[where f="mpoly_to_poly 1"]) simp_all
  have lo: "degree ?p \<le> degree (bivariate_as_poly_poly F)"
    using cnz mapc[of "degree ?p"] by (simp add: le_degree)
  have hi: "degree (bivariate_as_poly_poly F) \<le> degree ?p"
  proof (rule Polynomial.degree_le)
    show "\<forall>k>degree ?p. coeff (bivariate_as_poly_poly F) k = 0"
      by (auto simp: mapc coeff_eq_0)
  qed
  show ?thesis using lo hi by simp
qed

lemma degree_mpoly_to_poly_le:
  "Polynomial.degree (mpoly_to_poly i F) \<le> MPoly_Type.degree F i"
proof (rule Polynomial.degree_le)
  show "\<forall>j>MPoly_Type.degree F i. coeff (mpoly_to_poly i F) j = 0"
  proof (intro allI impI)
    fix j assume j: "MPoly_Type.degree F i < j"
    show "coeff (mpoly_to_poly i F) j = 0"
    proof (rule ccontr)
      assume "coeff (mpoly_to_poly i F) j \<noteq> 0"
      then have "MPoly_Type.coeff F (Poly_Mapping.single i j) \<noteq> 0"
        by simp
      then have "MPoly_Type.degree F i \<ge> j"
        using degree_geI[of F "Poly_Mapping.single i j" i] by simp
      with j show False by simp
    qed
  qed
qed

lemma pure_second_exception_bound:
  assumes "vars F \<subseteq> {1}" "F \<noteq> 0"
  shows "card {a. specialize_second a F = 0} \<le> MPoly_Type.degree F 1"
proof -
  let ?p = "mpoly_to_poly 1 F"
  have nz: "?p \<noteq> 0" using assms pure_second_polynomial_nonzero by blast
  have eq: "{a. specialize_second a F = 0} = {a. poly ?p a = 0}"
    using specialize_pure_second[OF assms(1)] by auto
  show ?thesis unfolding eq
    using poly_roots_degree[OF nz] degree_mpoly_to_poly_le[of 1 F] by linarith
qed


lemma pure_second_bad_indices_bound:
  fixes I :: "'index set"
  assumes "finite I" "inj_on second I" "vars F \<subseteq> {1}" "F \<noteq> 0"
  shows "card {k \<in> I. specialize_second (second k) F = 0} \<le> MPoly_Type.degree F 1"
proof -
  let ?bad = "{k \<in> I. specialize_second (second k) F = 0}"
  let ?roots = "{a. specialize_second a F = 0}"
  have roots: "finite ?roots"
    using assms(3,4) specialize_pure_second[of F]
      pure_second_polynomial_nonzero[of F] poly_roots_finite[of "mpoly_to_poly 1 F"]
    by auto
  have "card ?bad = card (second ` ?bad)"
    using assms(2) by (simp add: card_image inj_on_subset)
  also have "... \<le> card ?roots"
    by (rule card_mono[OF roots]) auto
  also have "... \<le> MPoly_Type.degree F 1"
    by (rule pure_second_exception_bound[OF assms(3,4)])
  finally show ?thesis .
qed


lemma bivariate_irreducible_factorization:
  fixes F :: "complex mpoly"
  assumes "bivariate F" "F \<noteq> 0"
  shows "\<exists>U Fs. U dvd 1 \<and> F = U * prod_list Fs \<and>
    (\<forall>G \<in> set Fs. bivariate G \<and> irreducible G)"
  using assms
proof (induct "MPoly_Type.degree F 0 + MPoly_Type.degree F 1" arbitrary: F rule: less_induct)
  case less
  show ?case
  proof (cases "F dvd 1")
    case True
    then show ?thesis
      by (intro exI[of _ F] exI[of _ "[]"]) simp
  next
    case nonunit: False
    show ?thesis
    proof (cases "irreducible F")
      case True
      then show ?thesis
        by (intro exI[of _ 1] exI[of _ "[F]"]) (simp add: less.prems)
    next
      case False
      then obtain A B where split: "F = A * B" "\<not> A dvd 1" "\<not> B dvd 1"
        using nonunit less.prems(2) by (meson irreducibleI)
      have nz: "A \<noteq> 0" "B \<noteq> 0" using split less.prems(2) by auto
      have bv: "bivariate A" "bivariate B"
        using bivariate_factors[OF nz] less.prems(1) split(1) by auto
      have pos: "0 < MPoly_Type.degree A 0 + MPoly_Type.degree A 1"
        "0 < MPoly_Type.degree B 0 + MPoly_Type.degree B 1"
        using nonunit_bivariate_degree_pos[OF bv(1) nz(1) split(2)]
          nonunit_bivariate_degree_pos[OF bv(2) nz(2) split(3)] by auto
      have measure: "MPoly_Type.degree F 0 + MPoly_Type.degree F 1 =
        (MPoly_Type.degree A 0 + MPoly_Type.degree A 1) +
        (MPoly_Type.degree B 0 + MPoly_Type.degree B 1)"
        using split nz by (simp add: mpoly_degree_mult_eq)
      have ma: "MPoly_Type.degree A 0 + MPoly_Type.degree A 1 <
        MPoly_Type.degree F 0 + MPoly_Type.degree F 1"
        using measure pos by linarith
      have mb: "MPoly_Type.degree B 0 + MPoly_Type.degree B 1 <
        MPoly_Type.degree F 0 + MPoly_Type.degree F 1"
        using measure pos by linarith
      obtain UA As where fa: "UA dvd 1" "A = UA * prod_list As"
        "\<forall>G \<in> set As. bivariate G \<and> irreducible G"
        using less.hyps ma bv(1) nz(1) by blast
      obtain UB Bs where fb: "UB dvd 1" "B = UB * prod_list Bs"
        "\<forall>G \<in> set Bs. bivariate G \<and> irreducible G"
        using less.hyps mb bv(2) nz(2) by blast
      obtain VA where ua: "1 = UA * VA" using fa(1) unfolding dvd_def by blast
      obtain VB where ub: "1 = UB * VB" using fb(1) unfolding dvd_def by blast
      have "UA * UB dvd 1"
      proof -
        have "1 = (UA * UB) * (VA * VB)" using ua ub by (simp add: mult_ac)
        then show ?thesis unfolding dvd_def by blast
      qed
      moreover have "F = (UA * UB) * prod_list (As @ Bs)"
        using split(1) fa(2) fb(2) by (simp add: mult_ac)
      moreover have "\<forall>G \<in> set (As @ Bs). bivariate G \<and> irreducible G"
        using fa(3) fb(3) by auto
      ultimately show ?thesis by blast
    qed
  qed
qed


lemma prod_list_partition_mpoly:
  fixes Fs :: "complex mpoly list"
  shows "prod_list Fs = prod_list (filter P Fs) * prod_list (filter (\<lambda>F. \<not> P F) Fs)"
  by (induct Fs) (auto simp: mult_ac)

lemma vars_prod_list_subset:
  fixes Fs :: "complex mpoly list"
  assumes "\<And>F. F \<in> set Fs \<Longrightarrow> vars F \<subseteq> S"
  shows "vars (prod_list Fs) \<subseteq> S"
  using assms
proof (induct Fs)
  case Nil
  then show ?case by simp
next
  case (Cons F Fs)
  have a: "vars F \<subseteq> S" using Cons.prems by auto
  have b: "vars (prod_list Fs) \<subseteq> S" using Cons.hyps Cons.prems by auto
  have "vars (F * prod_list Fs) \<subseteq> vars F \<union> vars (prod_list Fs)"
    by (rule vars_mult)
  with a b show ?case by (simp; blast)
qed

lemma bivariate_degree_first_zero:
  assumes "bivariate F" "MPoly_Type.degree F 0 = 0"
  shows "vars F \<subseteq> {1}"
  using assms unfolding bivariate_def by (auto simp: degree_eq_0_iff)


lemma green_factorization:
  fixes F :: "complex mpoly"
  assumes "bivariate F" "F \<noteq> 0"
  shows "\<exists>F0 Fs. F = F0 * prod_list Fs \<and> F0 \<noteq> 0 \<and>
    vars F0 \<subseteq> {1} \<and>
    (\<forall>G \<in> set Fs. bivariate G \<and> irreducible G \<and> 0 < MPoly_Type.degree G 0)"
proof -
  obtain U Gs where f: "U dvd 1" "F = U * prod_list Gs"
    "\<forall>G \<in> set Gs. bivariate G \<and> irreducible G"
    using bivariate_irreducible_factorization[OF assms] by blast
  let ?Z = "filter (\<lambda>G. MPoly_Type.degree G 0 = 0) Gs"
  let ?P = "filter (\<lambda>G. MPoly_Type.degree G 0 \<noteq> 0) Gs"
  have uv: "vars U = {}"
    using f(1) by (auto elim!: mpoly_is_unitE)
  have zv: "\<And>G. G \<in> set ?Z \<Longrightarrow> vars G \<subseteq> {1}"
    using f(3) bivariate_degree_first_zero by auto
  have f0v: "vars (U * prod_list ?Z) \<subseteq> {1}"
    using uv vars_prod_list_subset[OF zv] vars_mult[of U "prod_list ?Z"]
    by blast
  have eq: "F = (U * prod_list ?Z) * prod_list ?P"
    using f(2) prod_list_partition_mpoly[of Gs "\<lambda>G. MPoly_Type.degree G 0 = 0"]
    by (simp add: mult_ac)
  have nz: "U * prod_list ?Z \<noteq> 0" using eq assms(2) by auto
  have pf: "\<forall>G \<in> set ?P. bivariate G \<and> irreducible G \<and>
    0 < MPoly_Type.degree G 0"
    using f(3) by auto
  show ?thesis using eq nz f0v pf by blast
qed


lemma mpoly_to_mpoly_poly_pure:
  assumes "vars G \<subseteq> {i}"
  shows "mpoly_to_mpoly_poly i G = map_poly Const (mpoly_to_poly i G)"
proof (rule poly_eqI)
  fix k
  have "vars (coeff (mpoly_to_mpoly_poly i G) k) = {}"
    using vars_coeff_mpoly_to_mpoly_poly[of i G k] assms by auto
  then obtain c where c: "coeff (mpoly_to_mpoly_poly i G) k = Const c"
    by (rule vars_emptyE) blast
  have "c = coeff (mpoly_to_poly i G) k"
    using coeff_coeff_mpoly_to_mpoly_poly[of i G k 0] c
    by (simp add: mpoly_coeff_Const)
  with c show "coeff (mpoly_to_mpoly_poly i G) k =
    coeff (map_poly Const (mpoly_to_poly i G)) k"
    by (simp add: coeff_map_poly)
qed


lemma pure_second_root_divisor:
  fixes G :: "complex mpoly"
  assumes "vars G \<subseteq> {1}" "specialize_second a G = 0"
  shows "Var 1 - Const a dvd G"
proof -
  have root: "poly (mpoly_to_poly 1 G) a = 0"
    using assms specialize_pure_second[of G a] by simp
  obtain q where q: "mpoly_to_poly 1 G = [:-a, 1:] * q"
    using root by (meson dvdE poly_eq_0_iff_dvd)
  interpret h: map_poly_comm_ring_hom "(Const :: complex \<Rightarrow> complex mpoly)"
    by (unfold_locales; simp add: mpoly_Const_add mpoly_Const_mult)
  have lift: "map_poly Const [:-a, 1:] = [:-Const a, 1:]"
    by (simp add: h.map_poly_pCons_hom mpoly_Const_uminus)
  have eq: "mpoly_to_mpoly_poly 1 G = [:-Const a, 1:] * map_poly Const q"
  proof -
    have "mpoly_to_mpoly_poly 1 G = map_poly Const ([:-a, 1:] * q)"
      using mpoly_to_mpoly_poly_pure[OF assms(1)] q by simp
    also have "... = map_poly Const [:-a, 1:] * map_poly Const q"
      by (rule h.hom_mult)
    also have "... = [:-Const a, 1:] * map_poly Const q"
      by (simp add: lift)
    finally show ?thesis .
  qed
  have lin: "mpoly_to_mpoly_poly 1 (Var 1 - Const a) = [:-Const a, 1:]"
    by simp
  have dvd: "mpoly_to_mpoly_poly 1 (Var 1 - Const a) dvd mpoly_to_mpoly_poly 1 G"
    using eq lin by (metis dvdI)
  show ?thesis using dvd mpoly_to_mpoly_poly_dvd_iff[of 1 "Var 1 - Const a" G]
    by blast
qed


lemma bivariate_specialization_zero_divisor:
  fixes F :: "complex mpoly"
  assumes "bivariate F" "specialize_second a F = 0"
  shows "Var 1 - Const a dvd F"
proof -
  let ?D = "Var 1 - Const a"
  let ?p = "mpoly_to_mpoly_poly 0 F"
  have roots: "\<forall>k. insertion (\<lambda>_. a) (coeff ?p k) = 0"
    using assms(2) specialize_first_eq_zero_iff[of "\<lambda>_. a" 0 F] by simp
  have cdiv: "\<forall>k. ?D dvd coeff ?p k"
  proof
    fix k
    have v: "vars (coeff ?p k) \<subseteq> {1}"
      using bivariate_coeff_first[OF assms(1)] .
    have r: "poly (mpoly_to_poly 1 (coeff ?p k)) a = 0"
      using roots poly_eq_insertion[OF v] by simp
    have "specialize_second a (coeff ?p k) = 0"
      using r specialize_pure_second[OF v] by simp
    then show "?D dvd coeff ?p k"
      using pure_second_root_divisor[OF v] by simp
  qed
  have dvd: "[:?D:] dvd ?p" using cdiv by (simp add: const_poly_dvd_iff)
  have eq: "mpoly_to_mpoly_poly 0 ?D = [:?D:]" by simp
  have "mpoly_to_mpoly_poly 0 ?D dvd mpoly_to_mpoly_poly 0 F"
    using dvd by (simp add: eq)
  then show ?thesis by (simp only: mpoly_to_mpoly_poly_dvd_iff)
qed


lemma irreducible_specialize_second_nonzero:
  fixes F :: "complex mpoly"
  assumes "bivariate F" "irreducible F" "0 < MPoly_Type.degree F 0"
  shows "specialize_second a F \<noteq> 0"
proof
  assume z: "specialize_second a F = 0"
  let ?D = "Var 1 - Const a"
  have div: "?D dvd F" using bivariate_specialization_zero_divisor[OF assms(1) z] .
  have d0: "MPoly_Type.degree ?D 0 = 0"
    using degree_mpoly_to_mpoly_poly[of 0 ?D] by simp
  have d1: "MPoly_Type.degree ?D 1 = 1"
    using degree_mpoly_to_mpoly_poly[of 1 ?D] by simp
  have dnz: "?D \<noteq> 0" using d1 by auto
  have dn: "\<not> ?D dvd 1"
  proof
    assume "?D dvd 1"
    then obtain c where "?D = Const c" by (elim mpoly_is_unitE) blast
    with d1 show False by simp
  qed
  obtain H where fac: "F = ?D * H" using div by (elim dvdE) blast
  have hn: "H \<noteq> 0" using fac assms(2) unfolding irreducible_def by auto
  have "H dvd 1" using irreducibleD[OF assms(2) fac] dn by blast
  then obtain c where h: "H = Const c" by (elim mpoly_is_unitE) blast
  have "MPoly_Type.degree F 0 = MPoly_Type.degree ?D 0 + MPoly_Type.degree H 0"
    using fac hn dnz by (simp add: mpoly_degree_mult_eq)
  with d0 h assms(3) show False by simp
qed


lemma green_factorization_regular:
  fixes F :: "complex mpoly"
  assumes "bivariate F" "F \<noteq> 0"
  obtains F0 Fs where
    "F = F0 * prod_list Fs" "F0 \<noteq> 0" "vars F0 \<subseteq> {1}"
    "\<And>G. G \<in> set Fs \<Longrightarrow> bivariate G \<and> irreducible G \<and>
      0 < MPoly_Type.degree G 0 \<and> (\<forall>a. specialize_second a G \<noteq> 0)"
proof -
  obtain F0 Fs where f: "F = F0 * prod_list Fs" "F0 \<noteq> 0"
    "vars F0 \<subseteq> {1}"
    "\<forall>G \<in> set Fs. bivariate G \<and> irreducible G \<and>
      0 < MPoly_Type.degree G 0"
    using green_factorization[OF assms] by blast
  have reg: "\<And>G. G \<in> set Fs \<Longrightarrow> bivariate G \<and> irreducible G \<and>
    0 < MPoly_Type.degree G 0 \<and> (\<forall>a. specialize_second a G \<noteq> 0)"
    using f(4) irreducible_specialize_second_nonzero by blast
  show thesis by (rule that[OF f(1) f(2) f(3) reg])
qed

end
