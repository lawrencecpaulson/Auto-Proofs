(*  Title:      Gelfond_Schneider/GS_House.thy
    Author:     OpenAI Codex

A local house-style wrapper around min_int_poly roots for the direct
Gelfond-Schneider contradiction.
*)

theory GS_House
  imports GS_Preliminaries
begin

definition gs_house :: "complex \<Rightarrow> real"
  where "gs_house x \<equiv> Max (insert 0 (cmod ` set (complex_roots_of_int_poly (min_int_poly x))))"

lemma gs_house_nonneg [simp]: "0 \<le> gs_house x"
  by (simp add: gs_house_def)

lemma cmod_le_gs_house_of_root:
  assumes "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  shows "cmod z \<le> gs_house x"
  by (simp add: assms gs_house_def)

lemma self_le_gs_house:
  assumes alg: "algebraic x"
  shows "cmod x \<le> gs_house x"
  by (simp add: alg cmod_le_gs_house_of_root complex_roots_of_int_poly)

lemma min_int_poly_root_factorization:
  fixes x :: complex
  assumes alg: "algebraic x"
  shows "of_int_poly (min_int_poly x) =
    Polynomial.smult (of_int (Polynomial.lead_coeff (min_int_poly x)))
      (\<Prod> z\<in>set (complex_roots_of_int_poly (min_int_poly x)). [:-z, 1:])"
proof -
  let ?p = "min_int_poly x"
  have rsq: "rsquarefree (of_int_poly ?p :: complex poly)"
    by (rule irreducible_imp_rsquarefree_of_int_poly) (use alg in auto)
  have fac0: "Polynomial.smult (Polynomial.lead_coeff (of_int_poly ?p))
      (\<Prod> z | poly (of_int_poly ?p) z = 0. [:-z, 1:]) = (of_int_poly ?p :: complex poly)"
    by (rule complex_poly_decompose_rsquarefree[OF rsq])
  have roots_eq: "{z. poly (of_int_poly ?p) z = 0} = set (complex_roots_of_int_poly ?p)"
    using complex_roots_of_int_poly(1) alg by simp
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
      poly (of_int_poly (min_int_poly x)) 0"
    by (simp add: poly_0_coeff_0)
  also have "... = (\<Prod> z\<in>set (complex_roots_of_int_poly (min_int_poly x)). -z)"
    using fac by (simp add: poly_prod)
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
  have rootx: "x \<in> ?R"
    using complex_roots_of_int_poly(1) alg
    by (auto simp: min_int_poly_represents)
  have lt1: "cmod z < 1" if "z \<in> ?R" for z
    using no that by force
  have coeff0_eq: "of_int (Polynomial.coeff ?p 0) = (\<Prod> z\<in>?R. -z)"
    using ai min_int_poly_coeff0_eq_root_prod_of_algebraic_int
    by presburger
  have "Polynomial.coeff ?p 0 \<noteq> 0"
    using alg nz by (simp add: poly_0_coeff_0 [symmetric])
  then have coeff0_ge1: "1 \<le> cmod (Polynomial.coeff ?p 0)"
    by auto
  have rest_le1: "(\<Prod> z\<in>?R - {x}. cmod (-z)) \<le> 1"
    by (rule prod_le_1) (use lt1 in force)
  have "cmod (\<Prod> z\<in>?R. -z) < 1"
  proof -
    have nonneg_rest: "0 \<le> (\<Prod> z\<in>?R - {x}. cmod (-z))"
      by (rule prod_nonneg) auto
    have "cmod (\<Prod> z\<in>?R. -z) = cmod x * cmod (\<Prod> z\<in>?R - {x}. -z)"
      using rootx by (simp add: norm_mult prod.remove)
    also have "... \<le> cmod x * (\<Prod> z\<in>?R - {x}. cmod (-z))"
      by (metis order_refl prod_norm)
    also have "... \<le> cmod x"
      using \<open>x\<noteq>0\<close> rest_le1 by auto
    also have "... < 1"
      using lt1 rootx by blast
    finally show ?thesis .
  qed
  with coeff0_ge1 coeff0_eq show False
    by auto
qed

lemma one_le_gs_house_of_algebraic_int:
  fixes x :: complex
  assumes ai: "algebraic_int x"
  assumes nz: "x \<noteq> 0"
  shows "1 \<le> gs_house x"
proof -
  obtain z where z: "z \<in> set (complex_roots_of_int_poly (min_int_poly x))" "1 \<le> cmod z"
    using exists_gs_root_norm_ge_one_of_nonzero_algebraic_int[OF ai nz] by blast
  then show ?thesis
    using cmod_le_gs_house_of_root by force
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
  have prod_split: "(\<Prod>w\<in>?R. -w) = (-z) * (\<Prod>w\<in>?R - {z}. -w)"
    using zR by (simp add: prod.remove)
  have prod_rest_le: "(\<Prod>w\<in>?R - {z}. cmod (-w)) \<le> (\<Prod>w\<in>?R - {z}. gs_house x)"
    by (intro prod_mono) (auto intro: cmod_le_gs_house_of_root)
  have "cmod (Polynomial.coeff (min_int_poly x) 0) = cmod z * cmod (\<Prod>w\<in>?R - {z}. -w)"
    by (simp add: coeff0_eq prod_split norm_mult)
  also have "... \<le> cmod z * (\<Prod>w\<in>?R - {z}. gs_house x)"
    using prod_rest_le by (metis mult_left_mono norm_ge_zero prod_norm)
  also have "... = cmod z * gs_house x ^ (card ?R - 1)"
    by (simp add: zR)
  finally show ?thesis .
qed

lemma one_le_root_mul_house_pow_of_nonzero_algebraic_int:
  fixes x z :: complex
  assumes ai: "algebraic_int x"
  assumes nz: "x \<noteq> 0"
  assumes zR: "z \<in> set (complex_roots_of_int_poly (min_int_poly x))"
  shows "1 \<le> cmod z * gs_house x ^ (card (set (complex_roots_of_int_poly (min_int_poly x))) - 1)"
proof -
  have coeff0_nz: "Polynomial.coeff (min_int_poly x) 0 \<noteq> 0"
    using ai nz by (auto simp flip: poly_0_coeff_0)
  then have "1 \<le> cmod (of_int (Polynomial.coeff (min_int_poly x) 0) :: complex)"
    by fastforce
  also have "... \<le> cmod z * gs_house x ^ (card (set (complex_roots_of_int_poly (min_int_poly x))) - 1)"
    by (rule min_int_poly_coeff0_norm_le_root_mul_house_pow[OF ai zR])
  finally show ?thesis .
qed

lemma one_le_self_mul_house_pow_of_nonzero_algebraic_int:
  assumes ai: "algebraic_int x"
  assumes nz: "x \<noteq> 0"
  shows "1 \<le> cmod x * gs_house x ^ (card (set (complex_roots_of_int_poly (min_int_poly x))) - 1)"
proof -
  have root_mem: "x \<in> set (complex_roots_of_int_poly (min_int_poly x))"
    using ai by (auto simp: complex_roots_of_int_poly(1))
  show ?thesis
    using assms one_le_root_mul_house_pow_of_nonzero_algebraic_int root_mem
    by blast
qed

lemma gs_house_le_of_roots_le:
  fixes x :: complex
  assumes H_nonneg: "0 \<le> H"
  assumes roots_le:
    "\<And>z. z \<in> set (complex_roots_of_int_poly (min_int_poly x)) \<Longrightarrow> cmod z \<le> H"
  shows "gs_house x \<le> H"
  by (simp add: assms gs_house_def)

end
