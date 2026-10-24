theory Roth_Evaluation_Sandwich
  imports Roth_Taylor_Evaluation
begin

lemma roth_insertion_of_rat:
  fixes P :: "rat mpoly" and beta :: "nat \<Rightarrow> rat"
  shows "(of_rat (insertion beta P)::real) =
    insertion (\<lambda>v. of_rat (beta v)) (replace_coeff of_rat P)"
proof (induction P rule: mpoly_induct)
  case (monom I c)
  then show ?case
    by (simp add: replace_coeff_monom roth_insertion_monom_any
      of_rat_mult of_rat_prod of_rat_power)
next
  case (sum P Q I c)
  then show ?case
    by (simp add: replace_coeff_add insertion_add of_rat_add)
qed

lemma roth_integer_polynomial_cast:
  fixes P :: "int mpoly"
  shows "replace_coeff of_rat (replace_coeff (of_int::int \<Rightarrow> rat) P) =
    (replace_coeff (of_int::int \<Rightarrow> real) P)"
  by (simp add: roth_replace_coeff_comp o_def)

lemma roth_integer_evaluation_cast:
  fixes P :: "int mpoly" and beta :: "nat \<Rightarrow> rat"
  shows "(of_rat (insertion beta (replace_coeff (of_int::int \<Rightarrow> rat) P))::real) =
    insertion (\<lambda>v. of_rat (beta v)) (replace_coeff (of_int::int \<Rightarrow> real) P)"
  by (simp add: roth_insertion_of_rat roth_integer_polynomial_cast)

theorem roth_rational_evaluation_lower_exp:
  fixes beta :: "nat \<Rightarrow> rat" and P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "insertion beta (replace_coeff of_int P) \<noteq> (0::rat)"
  shows "exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v))) \<le>
    abs (insertion (\<lambda>v. of_rat (beta v))
      (replace_coeff (of_int::int \<Rightarrow> real) P))"
proof -
  have lower: "1 / (\<Prod>v<m. real (roth_rat_height (beta v)) ^ r v) \<le>
    abs (of_rat (insertion beta (replace_coeff of_int P))::real)"
    by (rule roth_rational_evaluation_lower_height_real[OF box nz])
  show ?thesis using lower
    by (simp add: roth_height_product_exp roth_integer_evaluation_cast)
qed

lemma roth_int_cast_keys_real:
  fixes P :: "int mpoly"
  shows "Poly_Mapping.keys (mapping_of (replace_coeff (of_int::int \<Rightarrow> real) P)) =
    Poly_Mapping.keys (mapping_of P)"
  by (auto simp: in_keys_iff MPoly_Type.coeff_def[symmetric] coeff_replace_coeff)

lemma roth_int_cast_box_real:
  fixes P :: "int mpoly"
  assumes "roth_poly_in_box m r P"
  shows "roth_poly_in_box m r (replace_coeff (of_int::int \<Rightarrow> real) P)"
  using assms by (simp add: roth_poly_in_box_def roth_int_cast_keys_real)

theorem roth_evaluation_sandwich:
  fixes P :: "int mpoly" and beta :: "nat \<Rightarrow> rat"
    and a h :: "nat \<Rightarrow> real"
  assumes box: "roth_poly_in_box m r P"
    and nz: "insertion beta (replace_coeff of_int P) \<noteq> (0::rat)"
    and B: "0 \<le> B"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and index: "ereal theta \<le> roth_index m r a
      (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and near: "\<And>v. abs (of_rat (beta v) - a v) \<le> exp (-kappa * h v)"
    and coeff: "\<And>I. I \<in> Poly_Mapping.keys
        (mapping_of (roth_translate a (replace_coeff (of_int::int \<Rightarrow> real) P)))
      \<Longrightarrow> abs (insertion a (roth_hasse I (replace_coeff (of_int::int \<Rightarrow> real) P))) \<le> B"
  shows "exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v))) \<le>
    B * real (card (Poly_Mapping.keys
      (mapping_of (roth_translate a (replace_coeff (of_int::int \<Rightarrow> real) P))))) *
      exp (-kappa * L * theta)"
proof -
  let ?R = "replace_coeff (of_int::int \<Rightarrow> real) P"
  let ?b = "\<lambda>v. of_rat (beta v)"
  have lower: "exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v))) \<le>
      abs (insertion ?b ?R)"
    by (rule roth_rational_evaluation_lower_exp[OF box nz])
  have upper: "abs (insertion ?b ?R) \<le>
      B * real (card (Poly_Mapping.keys (mapping_of (roth_translate a ?R)))) *
        exp (-kappa * L * theta)"
    by (rule roth_taylor_exponential_bound_box)
      (use box B rpos balance kpos Lpos index near coeff
        roth_int_cast_box_real[OF box] in auto)
  show ?thesis using lower upper by linarith
qed

end
