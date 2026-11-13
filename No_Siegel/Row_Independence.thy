theory Row_Independence
  imports Finite_Grid "Bivariate_Resultants.Resultant_Multiplicity"
begin

text \<open>Green, Section 3, proof of Lemma 3.1: summing the orders of
  specialised irreducible factors over the point configuration.\<close>

lemma sum_order_inj_on_le_degree:
  fixes p :: "complex poly"
  assumes fin: "finite I" and inj: "inj_on f I" and nz: "p \<noteq> 0"
  shows "(\<Sum>i\<in>I. Polynomial.order (f i) p) \<le> degree p"
proof -
  let ?roots = "{x. poly p x = 0}"
  have finite_roots: "finite ?roots" by (rule poly_roots_finite[OF nz])
  have image_finite: "finite (f ` I)" using fin by simp
  have "(\<Sum>i\<in>I. Polynomial.order (f i) p) =
      (\<Sum>x\<in>f ` I. Polynomial.order x p)"
    using sum.reindex[OF inj, of "\<lambda>x. Polynomial.order x p"]
    by simp
  also have "... = (\<Sum>x\<in>(f ` I) \<inter> ?roots. Polynomial.order x p)"
  proof -
    have "(\<Sum>x\<in>f ` I. Polynomial.order x p) =
        (\<Sum>x\<in>f ` I. if poly p x = 0 then Polynomial.order x p else 0)"
      by (rule sum.cong) (auto intro: order_0I)
    then show ?thesis by (simp add: sum.inter_restrict[OF image_finite])
  qed
  also have "... \<le> (\<Sum>x\<in>?roots. Polynomial.order x p)"
    by (rule sum_mono2[OF finite_roots]) auto
  also have "... \<le> degree p" by (rule sum_order_le_degree[OF nz])
  finally show ?thesis .
qed

lemma pair_eval_specialize_second:
  fixes F :: "complex mpoly"
  assumes "bivariate F"
  shows "poly (specialize_second (snd z) F) (fst z) = pair_eval F z"
proof -
  have "insertion (\<lambda>i. if i = 0 then fst z else snd z) F =
      insertion (\<lambda>i. if i = 0 then fst z else if i = 1 then snd z else 0) F"
    by (rule insertion_irrelevant_vars) (use assms in \<open>auto simp: bivariate_def\<close>)
  then show ?thesis
    by (simp add: poly_specialize_second pair_eval_def)
qed

lemma bivariate_total_degree_le:
  fixes F :: "complex mpoly"
  assumes "bivariate F"
  shows "total_degree F \<le>
    MPoly_Type.degree F 0 + MPoly_Type.degree F 1"
proof -
  have "total_degree F \<le> (\<Sum>v\<in>vars F. MPoly_Type.degree F v)"
    by (rule total_degree_bound)
  also have "... \<le> (\<Sum>v\<in>{0,1}. MPoly_Type.degree F v)"
    by (rule sum_mono2) (use assms in \<open>auto simp: bivariate_def\<close>)
  finally show ?thesis by simp
qed

lemma sum_list_pair_products_le:
  fixes f g :: "'a \<Rightarrow> nat"
  shows "sum_list (map (\<lambda>x. f x * g x) xs) \<le>
    sum_list (map f xs) * sum_list (map g xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "f x * g x + sum_list (map (\<lambda>y. f y * g y) xs) \<le>
      f x * g x + sum_list (map f xs) * sum_list (map g xs)"
    using Cons.hyps by simp
  also have "... \<le> (f x + sum_list (map f xs)) *
      (g x + sum_list (map g xs))"
    by (simp add: algebra_simps)
  finally show ?case by simp
qed

definition green_first_derivative ::
    "nat \<Rightarrow> complex mpoly \<Rightarrow> complex \<times> complex \<Rightarrow> complex" where
  "green_first_derivative j F z =
    poly (map_poly (insertion (\<lambda>_. snd z))
      ((pderiv ^^ j) (mpoly_to_mpoly_poly 0 F))) (fst z)"

definition green_factor_order_mass ::
    "complex mpoly list \<Rightarrow> complex \<times> complex \<Rightarrow> nat" where
  "green_factor_order_mass Fs z =
    sum_list (map (\<lambda>G. Polynomial.order (fst z)
      (specialize_second (snd z) G)) Fs)"

locale green_point_configuration =
  fixes I :: "'i set" and point :: "'i \<Rightarrow> complex \<times> complex" and J :: nat
  assumes finite_points: "finite I"
    and distinct_second: "inj_on (snd \<circ> point) I"
    and zero_count:
      "\<And>F::complex mpoly. F \<noteq> 0 \<Longrightarrow> bivariate F \<Longrightarrow>
        card {i \<in> I. pair_eval F (point i) = 0} \<le> J * total_degree F"
begin

lemma irreducible_factor_order_sum:
  fixes F :: "complex mpoly"
  assumes bv: "bivariate F" and irr: "irreducible F"
    and pos: "0 < MPoly_Type.degree F 0"
  shows "(\<Sum>i\<in>I. Polynomial.order (fst (point i))
      (specialize_second (snd (point i)) F)) \<le>
    J * total_degree F +
      2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
proof -
  let ?r = "first_resultant_poly F"
  have rnz: "?r \<noteq> 0"
    by (rule first_resultant_nonzero_irreducible[OF bv irr pos])
  have point_bound: "Polynomial.order (fst (point i))
      (specialize_second (snd (point i)) F) \<le>
      (if pair_eval F (point i) = 0 then 1 else 0) +
        Polynomial.order (snd (point i)) ?r"
    if "i \<in> I" for i
  proof (cases "pair_eval F (point i) = 0")
    case True
    then show ?thesis
      using first_resultant_multiplicity_irreducible[OF bv irr pos,
        where x="fst (point i)" and a="snd (point i)"]
      by simp
  next
    case False
    have "poly (specialize_second (snd (point i)) F) (fst (point i)) \<noteq> 0"
      using False pair_eval_specialize_second[OF bv] by simp
    then have "Polynomial.order (fst (point i))
        (specialize_second (snd (point i)) F) = 0"
      by (rule order_0I)
    with False show ?thesis by simp
  qed
  have count: "(\<Sum>i\<in>I. if pair_eval F (point i) = 0 then 1 else 0) =
      card {i \<in> I. pair_eval F (point i) = 0}"
  proof -
    have "{i \<in> I. pair_eval F (point i) = 0} =
        I \<inter> {i. pair_eval F (point i) = 0}" by auto
    then show ?thesis using finite_points by (simp add: sum.If_cases)
  qed
  have root_bound: "card {i \<in> I. pair_eval F (point i) = 0} \<le>
      J * total_degree F"
    using irr zero_count[OF _ bv] unfolding irreducible_def by blast
  have resultant_bound: "(\<Sum>i\<in>I. Polynomial.order (snd (point i)) ?r) \<le>
      2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
    using sum_order_inj_on_le_degree[OF finite_points distinct_second rnz]
      first_resultant_poly_degree_le[of F]
    by (simp add: o_def; linarith)
  have "(\<Sum>i\<in>I. Polynomial.order (fst (point i))
      (specialize_second (snd (point i)) F)) \<le>
      (\<Sum>i\<in>I. (if pair_eval F (point i) = 0 then 1 else 0) +
        Polynomial.order (snd (point i)) ?r)"
    by (rule sum_mono) (use point_bound in auto)
  also have "... = card {i \<in> I. pair_eval F (point i) = 0} +
      (\<Sum>i\<in>I. Polynomial.order (snd (point i)) ?r)"
    by (simp add: sum.distrib count)
  also have "... \<le> J * total_degree F +
      2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
    using root_bound resultant_bound by linarith
  finally show ?thesis .
qed

lemma factor_list_order_sum:
  fixes Fs :: "complex mpoly list"
  assumes factors: "\<And>G. G \<in> set Fs \<Longrightarrow>
      bivariate G \<and> irreducible G \<and> 0 < MPoly_Type.degree G 0"
  shows "(\<Sum>i\<in>I. green_factor_order_mass Fs (point i)) \<le>
    sum_list (map (\<lambda>G. J * total_degree G +
      2 * MPoly_Type.degree G 0 * MPoly_Type.degree G 1) Fs)"
  using factors
proof (induct Fs)
  case Nil
  then show ?case by (simp add: green_factor_order_mass_def)
next
  case (Cons G Fs)
  have G: "bivariate G" "irreducible G" "0 < MPoly_Type.degree G 0"
    using Cons.prems by auto
  have rest: "\<And>H. H \<in> set Fs \<Longrightarrow>
      bivariate H \<and> irreducible H \<and> 0 < MPoly_Type.degree H 0"
    using Cons.prems by auto
  have first: "(\<Sum>i\<in>I. Polynomial.order (fst (point i))
      (specialize_second (snd (point i)) G)) \<le>
      J * total_degree G +
        2 * MPoly_Type.degree G 0 * MPoly_Type.degree G 1"
    by (rule irreducible_factor_order_sum[OF G])
  have tail: "(\<Sum>i\<in>I. green_factor_order_mass Fs (point i)) \<le>
    sum_list (map (\<lambda>H. J * total_degree H +
      2 * MPoly_Type.degree H 0 * MPoly_Type.degree H 1) Fs)"
    by (rule Cons.hyps[OF rest])
  show ?case using first tail
    by (simp add: green_factor_order_mass_def sum.distrib; linarith)
qed

lemma factor_list_order_sum_degree:
  fixes Fs :: "complex mpoly list"
  assumes factors: "\<And>G. G \<in> set Fs \<Longrightarrow>
      bivariate G \<and> irreducible G \<and> 0 < MPoly_Type.degree G 0"
  shows "(\<Sum>i\<in>I. green_factor_order_mass Fs (point i)) \<le>
    J * (sum_list (map (\<lambda>G. MPoly_Type.degree G 0) Fs) +
      sum_list (map (\<lambda>G. MPoly_Type.degree G 1) Fs)) +
    2 * sum_list (map (\<lambda>G. MPoly_Type.degree G 0) Fs) *
      sum_list (map (\<lambda>G. MPoly_Type.degree G 1) Fs)"
proof -
  let ?d0 = "\<lambda>G. MPoly_Type.degree G 0"
  let ?d1 = "\<lambda>G. MPoly_Type.degree G 1"
  have term_bound: "J * total_degree G + 2 * ?d0 G * ?d1 G \<le>
      J * (?d0 G + ?d1 G) + 2 * ?d0 G * ?d1 G"
    if "G \<in> set Fs" for G
    using bivariate_total_degree_le factors that
    by (intro add_mono mult_le_mono1) auto
  have degree_sum: "sum_list (map (\<lambda>G. J * total_degree G +
      2 * ?d0 G * ?d1 G) Fs) \<le>
    sum_list (map (\<lambda>G. J * (?d0 G + ?d1 G) +
      2 * ?d0 G * ?d1 G) Fs)"
    by (rule sum_list_mono) (rule term_bound)
  have expression: "sum_list (map (\<lambda>G. J * (?d0 G + ?d1 G) +
      2 * ?d0 G * ?d1 G) Fs) =
    J * (sum_list (map ?d0 Fs) + sum_list (map ?d1 Fs)) +
    2 * sum_list (map (\<lambda>G. ?d0 G * ?d1 G) Fs)"
    by (induct Fs) (simp_all add: algebra_simps)
  have cross: "sum_list (map (\<lambda>G. ?d0 G * ?d1 G) Fs) \<le>
    sum_list (map ?d0 Fs) * sum_list (map ?d1 Fs)"
    by (rule sum_list_pair_products_le)
  have base: "(\<Sum>i\<in>I. green_factor_order_mass Fs (point i)) \<le>
    sum_list (map (\<lambda>G. J * total_degree G +
      2 * ?d0 G * ?d1 G) Fs)"
    by (rule factor_list_order_sum[where Fs=Fs]) (rule factors)
  show ?thesis
    using base degree_sum expression cross
    by linarith
qed

lemma nonexceptional_specialization_order:
  fixes F F0 :: "complex mpoly" and Fs :: "complex mpoly list"
  assumes factorization: "F = F0 * prod_list Fs"
    and pure: "vars F0 \<subseteq> {1}"
    and factors: "\<And>G. G \<in> set Fs \<Longrightarrow>
      bivariate G \<and> irreducible G \<and> 0 < MPoly_Type.degree G 0 \<and>
        (\<forall>a. specialize_second a G \<noteq> 0)"
    and good: "specialize_second (snd z) F0 \<noteq> 0"
    and vanishing: "\<forall>j<J. green_first_derivative j F z = 0"
  shows "J \<le> green_factor_order_mass Fs z"
proof -
  let ?a = "snd z"
  let ?x = "fst z"
  have regular: "\<And>G. G \<in> set Fs \<Longrightarrow> specialize_second ?a G \<noteq> 0"
    using factors by blast
  have product_nonzero: "specialize_second ?a (prod_list Fs) \<noteq> 0"
    by (rule specialize_first_prod_list_nonzero) (rule regular)
  have specialized: "specialize_second ?a F =
      specialize_second ?a F0 * specialize_second ?a (prod_list Fs)"
    using factorization by (simp add: specialize_first_mult)
  have specialized_nonzero: "specialize_second ?a F \<noteq> 0"
    using specialized good product_nonzero by simp
  have vanishes: "\<forall>j<J. poly (map_poly (insertion (\<lambda>_. ?a))
      ((pderiv ^^ j) (mpoly_to_mpoly_poly 0 F))) ?x = 0"
    using vanishing by (simp add: green_first_derivative_def)
  have multiplicity: "J \<le> Polynomial.order ?x (specialize_second ?a F)"
    by (rule specialized_derivatives_zero_imp_order[OF specialized_nonzero vanishes])
  have constant_order: "Polynomial.order ?x (specialize_second ?a F0) = 0"
  proof -
    have "specialize_second ?a F0 = [:poly (mpoly_to_poly 1 F0) ?a:]"
      by (rule specialize_pure_second[OF pure])
    with good have "poly (specialize_second ?a F0) ?x \<noteq> 0" by simp
    then show ?thesis by (rule order_0I)
  qed
  have product_order: "Polynomial.order ?x (specialize_second ?a (prod_list Fs)) =
      green_factor_order_mass Fs z"
    unfolding green_factor_order_mass_def
    by (rule order_specialize_first_prod_list) (rule regular)
  have "Polynomial.order ?x (specialize_second ?a F) =
      Polynomial.order ?x (specialize_second ?a F0) +
        Polynomial.order ?x (specialize_second ?a (prod_list Fs))"
    using specialized good product_nonzero by (simp add: order_mult)
  then show ?thesis using multiplicity constant_order product_order by simp
qed

lemma vanishing_polynomial_degree_bound:
  fixes F :: "complex mpoly"
  assumes bv: "bivariate F" and nz: "F \<noteq> 0"
    and vanishing: "\<And>i j. i \<in> I \<Longrightarrow> j < J \<Longrightarrow>
      green_first_derivative j F (point i) = 0"
  shows "J * card I \<le>
    J * (MPoly_Type.degree F 0 + MPoly_Type.degree F 1) +
      2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
proof -
  obtain F0 Fs where fac: "F = F0 * prod_list Fs"
    and f0nz: "F0 \<noteq> 0" and f0pure: "vars F0 \<subseteq> {1}"
    and factors: "\<And>G. G \<in> set Fs \<Longrightarrow>
      bivariate G \<and> irreducible G \<and>
      0 < MPoly_Type.degree G 0 \<and> (\<forall>a. specialize_second a G \<noteq> 0)"
    using bivariate_factorization_regular[OF bv nz] by blast
  let ?bad = "{i \<in> I. specialize_second (snd (point i)) F0 = 0}"
  let ?good = "I - ?bad"
  let ?A = "sum_list (map (\<lambda>G. MPoly_Type.degree G 0) Fs)"
  let ?B = "sum_list (map (\<lambda>G. MPoly_Type.degree G 1) Fs)"
  have bad_bound: "card ?bad \<le> MPoly_Type.degree F0 1"
  proof -
    have "card {i \<in> I. specialize_second ((snd \<circ> point) i) F0 = 0} \<le>
        MPoly_Type.degree F0 1"
      by (rule pure_second_bad_indices_bound[
        OF finite_points distinct_second f0pure f0nz])
    then show ?thesis by simp
  qed
  have bad_subset: "?bad \<subseteq> I" by auto
  have partition: "card ?good + card ?bad = card I"
  proof -
    have "card ?bad \<le> card I"
      by (rule card_mono[OF finite_points bad_subset])
    then show ?thesis
      using finite_points bad_subset by (simp add: card_Diff_subset)
  qed
  have good_order: "J \<le> green_factor_order_mass Fs (point i)"
    if "i \<in> ?good" for i
    by (rule nonexceptional_specialization_order[OF fac f0pure factors])
      (use that vanishing in auto)
  have good_sum: "J * card ?good \<le>
      (\<Sum>i\<in>?good. green_factor_order_mass Fs (point i))"
  proof -
    have "(\<Sum>i\<in>?good. J) \<le>
        (\<Sum>i\<in>?good. green_factor_order_mass Fs (point i))"
      by (rule sum_mono) (rule good_order, auto)
    then show ?thesis by (simp add: mult.commute)
  qed
  have all_sum: "(\<Sum>i\<in>I. green_factor_order_mass Fs (point i)) \<le>
      J * (?A + ?B) + 2 * ?A * ?B"
    using factor_list_order_sum_degree[where Fs=Fs]
    by (metis factors)
  have subset_sum: "(\<Sum>i\<in>?good. green_factor_order_mass Fs (point i)) \<le>
      (\<Sum>i\<in>I. green_factor_order_mass Fs (point i))"
    by (rule sum_mono2[OF finite_points]) auto
  have f0degree: "MPoly_Type.degree F0 0 = 0"
    using f0pure by (auto simp: degree_eq_0_iff)
  have factor_nz: "\<And>G. G \<in> set Fs \<Longrightarrow> G \<noteq> 0"
    using factors unfolding irreducible_def by blast
  have degrees0: "MPoly_Type.degree F 0 = ?A"
    using factor_product_degree[OF fac f0nz factor_nz, where i=0]
      f0degree by simp
  have degrees1: "MPoly_Type.degree F 1 = MPoly_Type.degree F0 1 + ?B"
    by (rule factor_product_degree[OF fac f0nz factor_nz])
  have card_budget: "card I \<le> card ?good + MPoly_Type.degree F0 1"
    using partition bad_bound by linarith
  have cross_budget: "?A * ?B \<le>
      MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
    using degrees0 degrees1 by (simp add: mult_left_mono)
  have "J * card I \<le> J * (card ?good + MPoly_Type.degree F0 1)"
    by (rule mult_left_mono[OF card_budget]) simp
  also have "... \<le> J * (?A + ?B + MPoly_Type.degree F0 1) +
      2 * ?A * ?B"
    using good_sum subset_sum all_sum by (simp add: algebra_simps; linarith)
  also have "... \<le>
      J * (MPoly_Type.degree F 0 + MPoly_Type.degree F 1) +
        2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
    using degrees0 degrees1 cross_budget by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma no_vanishing_polynomial:
  fixes F :: "complex mpoly"
  assumes dimension: "J * card I > 2 * R * S + J * (R + S)"
    and bv: "bivariate F"
    and degree_first: "MPoly_Type.degree F 0 \<le> R"
    and degree_second: "MPoly_Type.degree F 1 \<le> S"
    and vanishing: "\<And>i j. i \<in> I \<Longrightarrow> j < J \<Longrightarrow>
      green_first_derivative j F (point i) = 0"
  shows "F = 0"
proof (rule ccontr)
  assume "F \<noteq> 0"
  then have bound: "J * card I \<le>
    J * (MPoly_Type.degree F 0 + MPoly_Type.degree F 1) +
      2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
    by (rule vanishing_polynomial_degree_bound[OF bv _ vanishing])
  have product_bound: "MPoly_Type.degree F 0 * MPoly_Type.degree F 1 \<le>
      R * S"
    by (rule mult_le_mono[OF degree_first degree_second])
  have sum_bound: "MPoly_Type.degree F 0 + MPoly_Type.degree F 1 \<le>
      R + S"
    using degree_first degree_second by simp
  have scaled_sum: "J * (MPoly_Type.degree F 0 + MPoly_Type.degree F 1) \<le>
      J * (R + S)"
    by (rule mult_left_mono[OF sum_bound]) simp
  have scaled_product: "2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1 \<le>
      2 * R * S"
    using product_bound by (simp add: mult_left_mono mult.assoc)
  have "J * card I \<le> 2 * R * S + J * (R + S)"
    using bound scaled_sum scaled_product by linarith
  with dimension show False by simp
qed

end

end
