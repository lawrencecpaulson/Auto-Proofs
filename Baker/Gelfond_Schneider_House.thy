(*  Title:      Baker/Gelfond_Schneider_House.thy
    Author:     OpenAI Codex

A local house-style wrapper around min_int_poly roots for the direct
Gelfond-Schneider contradiction.
*)

theory Gelfond_Schneider_House
  imports Gelfond_Schneider_Preliminaries
begin

definition gs_house :: "complex \<Rightarrow> real"
  where "gs_house x = Max (insert 0 (cmod ` set (complex_roots_of_int_poly (min_int_poly x))))"

lemma gs_house_nonneg [simp]: "0 \<le> gs_house x"
proof -
  have fin: "finite (insert 0 (cmod ` set (complex_roots_of_int_poly (min_int_poly x))))"
    by simp
  have mem: "0 \<in> insert 0 (cmod ` set (complex_roots_of_int_poly (min_int_poly x)))"
    by simp
  show ?thesis
    unfolding gs_house_def by (rule Max_ge[OF fin mem])
qed

lemma cmod_le_gs_house_of_root:
  assumes "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  shows "cmod z \<le> gs_house x"
proof -
  have fin: "finite (insert 0 (cmod ` set (complex_roots_of_int_poly (min_int_poly x))))"
    by simp
  have mem: "cmod z \<in> insert 0 (cmod ` set (complex_roots_of_int_poly (min_int_poly x)))"
    using assms by auto
  show ?thesis
    unfolding gs_house_def by (rule Max_ge[OF fin mem])
qed

lemma self_le_gs_house:
  assumes alg: "algebraic x"
  shows "cmod x \<le> gs_house x"
proof -
  have root_mem: "x \<in> set (complex_roots_of_int_poly (min_int_poly x))"
    using complex_roots_of_int_poly(1)[of "min_int_poly x"] assms
    by (auto simp: min_int_poly_represents)
  show ?thesis
    by (rule cmod_le_gs_house_of_root[OF root_mem])
qed

lemma min_int_poly_root_factorization:
  fixes x :: complex
  assumes alg: "algebraic x"
  shows "of_int_poly (min_int_poly x) =
    Polynomial.smult (of_int (Polynomial.lead_coeff (min_int_poly x)))
      (\<Prod> z\<in>set (complex_roots_of_int_poly (min_int_poly x)). [:-z, 1:])"
proof -
  let ?p = "min_int_poly x"
  have pdeg: "Polynomial.degree ?p > 0"
    using alg by auto
  have p0: "?p \<noteq> 0"
    using pdeg by auto
  have rsq: "rsquarefree (of_int_poly ?p :: complex poly)"
    by (rule irreducible_imp_rsquarefree_of_int_poly) (use alg pdeg in auto)
  have fac0: "Polynomial.smult (Polynomial.lead_coeff (of_int_poly ?p))
      (\<Prod> z | poly (of_int_poly ?p) z = 0. [:-z, 1:]) = (of_int_poly ?p :: complex poly)"
    by (rule complex_poly_decompose_rsquarefree[OF rsq])
  have roots_eq: "{z. poly (of_int_poly ?p) z = 0} = set (complex_roots_of_int_poly ?p)"
    using complex_roots_of_int_poly(1)[OF p0] by simp
  have fac_set: "Polynomial.smult (Polynomial.lead_coeff (of_int_poly ?p))
      (\<Prod> z\<in>set (complex_roots_of_int_poly ?p). [:-z, 1:]) = of_int_poly ?p"
    using fac0 by (simp add: roots_eq)
  show ?thesis
    using fac_set by simp
qed

lemma min_int_poly_coeff0_eq_root_prod_of_algebraic_int:
  fixes x :: complex
  assumes ai: "algebraic_int x"
  shows "of_int (Polynomial.coeff (min_int_poly x) 0) =
    (\<Prod> z\<in>set (complex_roots_of_int_poly (min_int_poly x)). -z)"
proof -
  have alg: "algebraic x"
    using ai by auto
  have lc1: "Polynomial.lead_coeff (min_int_poly x) = 1"
    by (rule lead_coeff_min_int_poly_eq_1_of_algebraic_int) (rule ai)
  have fac: "of_int_poly (min_int_poly x) =
      (\<Prod> z\<in>set (complex_roots_of_int_poly (min_int_poly x)). [:-z, 1:])"
    using min_int_poly_root_factorization[OF alg] lc1 by simp
  have "of_int (Polynomial.coeff (min_int_poly x) 0) =
      poly (of_int_poly (min_int_poly x)) (0 :: complex)"
    by (simp add: poly_0_coeff_0)
  also have "... = poly (\<Prod> z\<in>set (complex_roots_of_int_poly (min_int_poly x)). [:-z, 1:]) 0"
    using fac by simp
  also have "... = (\<Prod> z\<in>set (complex_roots_of_int_poly (min_int_poly x)). poly [:-z, 1:] 0)"
    by (simp add: poly_prod)
  also have "... = (\<Prod> z\<in>set (complex_roots_of_int_poly (min_int_poly x)). -z)"
    by simp
  finally show ?thesis .
qed

lemma exists_gs_root_norm_ge_one_of_nonzero_algebraic_int:
  fixes x :: complex
  assumes ai: "algebraic_int x"
  assumes nz: "x \<noteq> 0"
  shows "\<exists> z \<in> set (complex_roots_of_int_poly (min_int_poly x)). 1 \<le> cmod z"
proof (rule ccontr)
  let ?p = "min_int_poly x"
  let ?R = "set (complex_roots_of_int_poly ?p)"
  assume no: "\<not> (\<exists>z\<in>?R. 1 \<le> cmod z)"
  have alg: "algebraic x"
    using ai by auto
  have pdeg: "Polynomial.degree ?p > 0"
    using alg by auto
  have p0: "?p \<noteq> 0"
    using pdeg by auto
  have rootx: "x \<in> ?R"
    using complex_roots_of_int_poly(1)[OF p0] alg
    by (auto simp: min_int_poly_represents)
  have lt1: "cmod z < 1" if "z \<in> ?R" for z
    using no that by force
  have le1: "cmod z \<le> 1" if "z \<in> ?R" for z
    using lt1[OF that] by linarith
  have x_lt1: "cmod x < 1"
    by (rule lt1[OF rootx])
  have lc1: "Polynomial.lead_coeff ?p = 1"
    by (rule lead_coeff_min_int_poly_eq_1_of_algebraic_int) (rule ai)
  have fac: "of_int_poly ?p = (\<Prod> z\<in>?R. [:-z, 1:])"
    using min_int_poly_root_factorization[OF alg] lc1 by simp
  have coeff0_eq: "of_int (Polynomial.coeff ?p 0) = (\<Prod> z\<in>?R. -z)"
  proof -
    have "of_int (Polynomial.coeff ?p 0) = poly (of_int_poly ?p) (0 :: complex)"
      by (simp add: poly_0_coeff_0)
    also have "... = poly (\<Prod> z\<in>?R. [:-z, 1:]) 0"
      using fac by simp
    also have "... = (\<Prod> z\<in>?R. poly [:-z, 1:] 0)"
      by (simp add: poly_prod)
    also have "... = (\<Prod> z\<in>?R. -z)"
      by simp
    finally show ?thesis .
  qed
  have coeff0_nz: "Polynomial.coeff ?p 0 \<noteq> 0"
    using alg nz by (simp add: poly_0_coeff_0 [symmetric])
  have coeff0_ge1_int: "1 \<le> abs (Polynomial.coeff ?p 0)"
  proof -
    have "0 < abs (Polynomial.coeff ?p 0)"
      using coeff0_nz by simp
    then show ?thesis
      by simp
  qed
  have coeff0_ge1: "1 \<le> cmod (of_int (Polynomial.coeff ?p 0) :: complex)"
    using coeff0_ge1_int by simp
  have rest_le1: "(\<Prod> z\<in>?R - {x}. cmod (-z)) \<le> 1"
    by (rule prod_le_1) (use le1 in auto)
  have rest_norm_le: "cmod (\<Prod> z\<in>?R - {x}. -z) \<le> (\<Prod> z\<in>?R - {x}. cmod (-z))"
    by (rule norm_prod_le)
  have prod_norm_lt1: "cmod (\<Prod> z\<in>?R. -z) < 1"
  proof -
    have finR: "finite ?R"
      by simp
    have nonneg_rest: "0 \<le> (\<Prod> z\<in>?R - {x}. cmod (-z))"
      by (rule prod_nonneg) auto
    have "cmod (\<Prod> z\<in>?R. -z) = cmod ((-x) * (\<Prod> z\<in>?R - {x}. -z))"
      using rootx finR by (simp add: prod.remove)
    also have "... = cmod x * cmod (\<Prod> z\<in>?R - {x}. -z)"
      by (simp add: norm_mult)
    also have "... \<le> cmod x * (\<Prod> z\<in>?R - {x}. cmod (-z))"
      using rest_norm_le by (intro mult_left_mono) auto
    also have "... \<le> cmod x"
    proof -
      have "(\<Prod> z\<in>?R - {x}. cmod (-z)) * cmod x \<le> cmod x"
        by (rule mult_left_le_one_le) (use rest_le1 nonneg_rest in auto)
      then show ?thesis
        by (simp add: mult.commute)
    qed
    also have "... < 1"
      by (rule x_lt1)
    finally show ?thesis .
  qed
  have "1 \<le> cmod (\<Prod> z\<in>?R. -z)"
    using coeff0_ge1 coeff0_eq by simp
  with prod_norm_lt1 show False
    by linarith
qed

lemma one_le_gs_house_of_algebraic_int:
  fixes x :: complex
  assumes ai: "algebraic_int x"
  assumes nz: "x \<noteq> 0"
  shows "1 \<le> gs_house x"
proof -
  obtain z where z: "z \<in> set (complex_roots_of_int_poly (min_int_poly x))" "1 \<le> cmod z"
    using exists_gs_root_norm_ge_one_of_nonzero_algebraic_int[OF ai nz] by blast
  have "cmod z \<le> gs_house x"
    by (rule cmod_le_gs_house_of_root[OF z(1)])
  with z(2) show ?thesis
    by linarith
qed

lemma min_int_poly_coeff0_norm_le_root_mul_house_pow:
  fixes x z :: complex
  assumes ai: "algebraic_int x"
  assumes zR: "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  shows "cmod (of_int (Polynomial.coeff (min_int_poly x) 0) :: complex) \<le>
    cmod z * gs_house x ^ (card (set (complex_roots_of_int_poly (min_int_poly x))) - 1)"
proof -
  let ?R = "set (complex_roots_of_int_poly (min_int_poly x))"
  have coeff0_eq: "of_int (Polynomial.coeff (min_int_poly x) 0) = (\<Prod>w\<in>?R. -w)"
    by (rule min_int_poly_coeff0_eq_root_prod_of_algebraic_int[OF ai])
  have finR: "finite ?R"
    by simp
  have prod_split: "(\<Prod>w\<in>?R. -w) = (-z) * (\<Prod>w\<in>?R - {z}. -w)"
    using finR zR by (simp add: prod.remove)
  have prod_rest_le: "(\<Prod>w\<in>?R - {z}. cmod (-w)) \<le> (\<Prod>w\<in>?R - {z}. gs_house x)"
    by (intro prod_mono) (auto intro: cmod_le_gs_house_of_root)
  have card_rest: "card (?R - {z}) = card ?R - 1"
    using finR zR by simp
  have "cmod (of_int (Polynomial.coeff (min_int_poly x) 0) :: complex) = cmod (\<Prod>w\<in>?R. -w)"
    using coeff0_eq by simp
  also have "... = cmod ((-z) * (\<Prod>w\<in>?R - {z}. -w))"
    by (simp add: prod_split)
  also have "... = cmod z * cmod (\<Prod>w\<in>?R - {z}. -w)"
    by (simp add: norm_mult)
  also have "... \<le> cmod z * (\<Prod>w\<in>?R - {z}. cmod (-w))"
    by (intro mult_left_mono norm_prod_le) simp
  also have "... \<le> cmod z * (\<Prod>w\<in>?R - {z}. gs_house x)"
    by (intro mult_left_mono prod_rest_le) simp
  also have "... = cmod z * gs_house x ^ card (?R - {z})"
    by simp
  also have "... = cmod z * gs_house x ^ (card ?R - 1)"
    by (simp add: card_rest)
  finally show ?thesis .
qed

lemma one_le_root_mul_house_pow_of_nonzero_algebraic_int:
  fixes x z :: complex
  assumes ai: "algebraic_int x"
  assumes nz: "x \<noteq> 0"
  assumes zR: "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  shows "1 \<le> cmod z * gs_house x ^ (card (set (complex_roots_of_int_poly (min_int_poly x))) - 1)"
proof -
  have alg: "algebraic x"
    using ai by auto
  have coeff0_nz: "Polynomial.coeff (min_int_poly x) 0 \<noteq> 0"
    using alg nz by (simp add: poly_0_coeff_0 [symmetric])
  have coeff0_ge1: "1 \<le> cmod (of_int (Polynomial.coeff (min_int_poly x) 0) :: complex)"
  proof -
    have "0 < abs (Polynomial.coeff (min_int_poly x) 0)"
      using coeff0_nz by simp
    then show ?thesis
      by simp
  qed
  also have "... \<le> cmod z * gs_house x ^ (card (set (complex_roots_of_int_poly (min_int_poly x))) - 1)"
    by (rule min_int_poly_coeff0_norm_le_root_mul_house_pow[OF ai zR])
  finally show ?thesis .
qed

lemma one_le_self_mul_house_pow_of_nonzero_algebraic_int:
  fixes x :: complex
  assumes ai: "algebraic_int x"
  assumes nz: "x \<noteq> 0"
  shows "1 \<le> cmod x * gs_house x ^ (card (set (complex_roots_of_int_poly (min_int_poly x))) - 1)"
proof -
  have alg: "algebraic x"
    using ai by auto
  have pdeg: "Polynomial.degree (min_int_poly x) > 0"
    using alg by auto
  have p0: "min_int_poly x \<noteq> 0"
    using pdeg by auto
  have root_mem: "x \<in> set (complex_roots_of_int_poly (min_int_poly x))"
    using complex_roots_of_int_poly(1)[OF p0] alg
    by (auto simp: min_int_poly_represents)
  show ?thesis
    by (rule one_le_root_mul_house_pow_of_nonzero_algebraic_int[OF ai nz root_mem])
qed

lemma gs_house_le_of_roots_le:
  fixes x :: complex
  assumes H_nonneg: "0 \<le> H"
  assumes roots_le:
    "\<And>z. z \<in> set (complex_roots_of_int_poly (min_int_poly x)) \<Longrightarrow> cmod z \<le> H"
  shows "gs_house x \<le> H"
proof -
  let ?S = "insert 0 (cmod ` set (complex_roots_of_int_poly (min_int_poly x)))"
  have fin: "finite ?S"
    by simp
  have ne: "?S \<noteq> {}"
    by simp
  have ub: "\<forall>y\<in>?S. y \<le> H"
  proof
    fix y
    assume yS: "y \<in> ?S"
    then consider (zero) "y = 0" | (root) z
      where "z \<in> set (complex_roots_of_int_poly (min_int_poly x))" "y = cmod z"
      by auto
    then show "y \<le> H"
    proof cases
      case zero
      with H_nonneg show ?thesis
        by simp
    next
      case (root z)
      with roots_le show ?thesis
        by simp
    qed
  qed
  show ?thesis
    unfolding gs_house_def
    by (rule Max.boundedI[OF fin ne]) (use ub in auto)
qed

end
