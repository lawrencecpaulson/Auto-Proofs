theory Bivariate_Resultant_Pairs
  imports Resultant_Multiplicity Factor_Algebraic_Polynomial.Roots_of_Algebraic_Poly
begin

section \<open>Resultants of two bivariate polynomials\<close>

text \<open>The first-variable resultant of two bivariate polynomials is a
  polynomial in the second variable. Fixed-size Sylvester matrices retain
  information at fibres where one of the degrees drops.\<close>

definition bivariate_pair_resultant :: "complex mpoly \<Rightarrow> complex mpoly \<Rightarrow> complex mpoly" where
  "bivariate_pair_resultant F G =
    resultant (mpoly_to_mpoly_poly 0 F) (mpoly_to_mpoly_poly 0 G)"

definition bivariate_pair_resultant_poly :: "complex mpoly \<Rightarrow> complex mpoly \<Rightarrow> complex poly" where
  "bivariate_pair_resultant_poly F G = mpoly_to_poly 1 (bivariate_pair_resultant F G)"

lemma vars_bivariate_pair_resultant:
  assumes F: "bivariate F" and G: "bivariate G"
  shows "vars (bivariate_pair_resultant F G) \<subseteq> {1}"
proof -
  have cF: "vars (coeff (mpoly_to_mpoly_poly 0 F) k) \<subseteq> {1}" for k
    by (rule bivariate_coeff_first[OF F])
  have cG: "vars (coeff (mpoly_to_mpoly_poly 0 G) k) \<subseteq> {1}" for k
    by (rule bivariate_coeff_first[OF G])
  show ?thesis
    unfolding bivariate_pair_resultant_def
    using vars_resultant[of "mpoly_to_mpoly_poly 0 F" "mpoly_to_mpoly_poly 0 G"]
      cF cG by blast
qed

lemma poly_bivariate_pair_resultant:
  assumes "bivariate F" "bivariate G"
  shows "poly (bivariate_pair_resultant_poly F G) a =
    insertion (\<lambda>_. a) (bivariate_pair_resultant F G)"
  using poly_eq_insertion[OF vars_bivariate_pair_resultant[OF assms]]
  by (simp add: bivariate_pair_resultant_poly_def)

lemma bivariate_pair_resultant_specialize_fixed_size:
  assumes "bivariate F" "bivariate G"
  shows "poly (bivariate_pair_resultant_poly F G) a =
    det (sylvester_mat_sub (MPoly_Type.degree F 0) (MPoly_Type.degree G 0)
      (specialize_second a F) (specialize_second a G))"
proof -
  let ?p = "mpoly_to_mpoly_poly 0 F"
  let ?q = "mpoly_to_mpoly_poly 0 G"
  let ?h = "insertion (\<lambda>_. a)"
  interpret h: comm_ring_hom ?h by (rule comm_ring_hom_insertion)
  have f: "map_poly ?h ?p = specialize_second a F"
    by (simp add: partial_insertion_def)
  have g: "map_poly ?h ?q = specialize_second a G"
    by (simp add: partial_insertion_def)
  have "poly (bivariate_pair_resultant_poly F G) a =
      ?h (resultant ?p ?q)"
    using poly_bivariate_pair_resultant[OF assms, of a]
    by (simp add: bivariate_pair_resultant_def)
  also have "... = ?h (resultant_sub (degree ?p) (degree ?q) ?p ?q)"
    by (simp add: resultant_def sylvester_mat_def resultant_sub_def)
  also have "... = resultant_sub (degree ?p) (degree ?q)
      (map_poly ?h ?p) (map_poly ?h ?q)"
    by (rule h.resultant_sub_map_poly)
  also have "... = det (sylvester_mat_sub (MPoly_Type.degree F 0)
      (MPoly_Type.degree G 0) (specialize_second a F) (specialize_second a G))"
    by (simp add: resultant_sub_def f g)
  finally show ?thesis .
qed

lemma bivariate_pair_resultant_specialize:
  assumes bv: "bivariate F" "bivariate G"
    and deg: "degree (specialize_second a F) = MPoly_Type.degree F 0"
      "degree (specialize_second a G) = MPoly_Type.degree G 0"
  shows "poly (bivariate_pair_resultant_poly F G) a =
    resultant (specialize_second a F) (specialize_second a G)"
  using bivariate_pair_resultant_specialize_fixed_size[OF bv, of a] deg
  by (simp add: resultant_def sylvester_mat_def)

lemma bivariate_pair_resultant_regular_zero_iff:
  assumes bv: "bivariate F" "bivariate G"
    and deg: "degree (specialize_second a F) = MPoly_Type.degree F 0"
      "degree (specialize_second a G) = MPoly_Type.degree G 0"
    and Gpos: "0 < MPoly_Type.degree G 0"
  shows "poly (bivariate_pair_resultant_poly F G) a = 0 \<longleftrightarrow>
    (\<exists>x. poly (specialize_second a F) x = 0 \<and>
      poly (specialize_second a G) x = 0)"
proof -
  have nz: "specialize_second a G \<noteq> 0" using deg(2) Gpos by auto
  show ?thesis
    using bivariate_pair_resultant_specialize[OF bv deg]
      resultant_zero_iff_common_root_complex[OF nz,
        of "specialize_second a F"] by simp
qed

lemma bivariate_pair_resultant_degree_le:
  "MPoly_Type.degree (bivariate_pair_resultant F G) 1 \<le>
    MPoly_Type.degree G 0 * MPoly_Type.degree F 1 +
    MPoly_Type.degree F 0 * MPoly_Type.degree G 1"
proof -
  have "MPoly_Type.degree
      (resultant (mpoly_to_mpoly_poly 0 F) (mpoly_to_mpoly_poly 0 G)) 1 \<le>
      degree (mpoly_to_mpoly_poly 0 G) * MPoly_Type.degree F 1 +
      degree (mpoly_to_mpoly_poly 0 F) * MPoly_Type.degree G 1"
    by (rule mpoly_degree_resultant_weighted_le)
      (rule degree_coeff_first_le)+
  then show ?thesis by (simp add: bivariate_pair_resultant_def)
qed

lemma bivariate_pair_resultant_poly_degree_le:
  "degree (bivariate_pair_resultant_poly F G) \<le>
    MPoly_Type.degree G 0 * MPoly_Type.degree F 1 +
    MPoly_Type.degree F 0 * MPoly_Type.degree G 1"
  using bivariate_pair_resultant_degree_le[of F G]
    degree_mpoly_to_poly_le[of 1 "bivariate_pair_resultant F G"]
  by (simp add: bivariate_pair_resultant_poly_def)

lemma bivariate_pair_resultant_bad_fibres_card:
  assumes nz: "bivariate_pair_resultant_poly F G \<noteq> 0"
  shows "card {a. poly (bivariate_pair_resultant_poly F G) a = 0} \<le>
    MPoly_Type.degree G 0 * MPoly_Type.degree F 1 +
    MPoly_Type.degree F 0 * MPoly_Type.degree G 1"
  using poly_roots_degree[OF nz] bivariate_pair_resultant_poly_degree_le[of F G]
  by linarith

lemma bivariate_pair_common_regular_fibres_card:
  assumes bv: "bivariate F" "bivariate G"
    and pos: "0 < MPoly_Type.degree G 0"
    and nz: "bivariate_pair_resultant_poly F G \<noteq> 0"
  shows "card {a. degree (specialize_second a F) = MPoly_Type.degree F 0 \<and>
      degree (specialize_second a G) = MPoly_Type.degree G 0 \<and>
      (\<exists>x. poly (specialize_second a F) x = 0 \<and>
        poly (specialize_second a G) x = 0)}
    \<le> MPoly_Type.degree G 0 * MPoly_Type.degree F 1 +
      MPoly_Type.degree F 0 * MPoly_Type.degree G 1"
proof -
  let ?S = "{a. degree (specialize_second a F) = MPoly_Type.degree F 0 \<and>
      degree (specialize_second a G) = MPoly_Type.degree G 0 \<and>
      (\<exists>x. poly (specialize_second a F) x = 0 \<and>
        poly (specialize_second a G) x = 0)}"
  let ?R = "{a. poly (bivariate_pair_resultant_poly F G) a = 0}"
  have sub: "?S \<subseteq> ?R"
  proof
    fix a assume "a \<in> ?S"
    then have deg: "degree (specialize_second a F) = MPoly_Type.degree F 0"
      "degree (specialize_second a G) = MPoly_Type.degree G 0"
      and common: "\<exists>x. poly (specialize_second a F) x = 0 \<and>
        poly (specialize_second a G) x = 0"
      by auto
    show "a \<in> ?R"
      using bivariate_pair_resultant_regular_zero_iff[OF bv deg pos] common
      by simp
  qed
  have "card ?S \<le> card ?R"
    by (rule card_mono[OF poly_roots_finite[OF nz] sub])
  also have "... \<le>
      MPoly_Type.degree G 0 * MPoly_Type.degree F 1 +
      MPoly_Type.degree F 0 * MPoly_Type.degree G 1"
    by (rule bivariate_pair_resultant_bad_fibres_card[OF nz])
  finally show ?thesis .
qed

lemma bivariate_irreducible_fibres_generically_squarefree:
  assumes bv: "bivariate F" and irr: "irreducible F"
    and pos: "0 < MPoly_Type.degree F 0"
  shows "card {a. degree (specialize_second a F) < MPoly_Type.degree F 0 \<or>
      \<not> rsquarefree (specialize_second a F)}
    \<le> 2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
proof -
  have nz: "specialize_second a F \<noteq> 0" for a
    by (rule irreducible_specialize_second_nonzero[OF bv irr pos])
  have root: "\<not> rsquarefree (specialize_second a F) \<longleftrightarrow>
      (\<exists>x. 2 \<le> Polynomial.order x (specialize_second a F))" for a
  proof
    assume "\<not> rsquarefree (specialize_second a F)"
    then obtain x where ord: "Polynomial.order x (specialize_second a F) \<noteq> 0"
      "Polynomial.order x (specialize_second a F) \<noteq> 1"
      using nz[of a] unfolding rsquarefree_def by blast
    have "2 \<le> Polynomial.order x (specialize_second a F)"
      using ord by arith
    then show "\<exists>x. 2 \<le> Polynomial.order x (specialize_second a F)"
      by blast
  next
    assume "\<exists>x. 2 \<le> Polynomial.order x (specialize_second a F)"
    then obtain x where ord: "2 \<le> Polynomial.order x (specialize_second a F)"
      by blast
    show "\<not> rsquarefree (specialize_second a F)"
    proof
      assume "rsquarefree (specialize_second a F)"
      then have "Polynomial.order x (specialize_second a F) = 0 \<or>
        Polynomial.order x (specialize_second a F) = 1"
        unfolding rsquarefree_def by blast
      with ord show False by arith
    qed
  qed
  have eq: "{a. degree (specialize_second a F) < MPoly_Type.degree F 0 \<or>
      \<not> rsquarefree (specialize_second a F)} =
      {a. exceptional_first_fibre F a}"
    by (auto simp: exceptional_first_fibre_def root)
  show ?thesis
    unfolding eq by (rule first_resultant_exceptional_fibre_card[OF bv irr pos])
qed

end
