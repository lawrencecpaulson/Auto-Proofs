theory Roth_Rational_Evaluation
  imports Roth_Auxiliary_Height
begin

section \<open>Denominators of polynomial evaluations at rational points\<close>

lemma roth_clear_power:
  fixes p q :: int
  assumes q: "q \<noteq> 0" and ir: "i \<le> r"
  shows "(of_int q::rat)^r * (of_int p / of_int q)^i =
    of_int (p^i * q^(r-i))"
proof -
  have "(of_int q::rat)^r = (of_int q)^i * (of_int q)^(r-i)"
    using ir by (simp add: power_add[symmetric])
  then show ?thesis using q
    by (simp add: power_divide field_simps)
qed

lemma roth_clear_monom_evaluation:
  fixes p q :: "nat \<Rightarrow> int" and c :: int
  assumes box: "I \<in> roth_exponent_box m r"
    and qpos: "\<And>v. v < m \<Longrightarrow> 0 < q v"
  shows "(\<Prod>v<m. (of_int (q v)::rat) ^ r v) *
    insertion (\<lambda>v. of_int (p v) / of_int (q v)) (MPoly_Type.monom I (of_int c)) =
    of_int (c * (\<Prod>v<m. p v ^ Poly_Mapping.lookup I v *
      q v ^ (r v - Poly_Mapping.lookup I v)))"
proof -
  have keys: "Poly_Mapping.keys I \<subseteq> {..<m}"
    by (rule roth_exponent_boxD(1)[OF box])
  have ipow: "(\<Prod>v\<in>Poly_Mapping.keys I.
      (of_int (p v) / of_int (q v)::rat) ^ Poly_Mapping.lookup I v) =
    (\<Prod>v<m. (of_int (p v) / of_int (q v)::rat) ^ Poly_Mapping.lookup I v)"
    using keys by (intro prod.mono_neutral_left) (auto simp: not_in_keys_iff_lookup_eq_zero)
  have point: "(of_int (q v)::rat)^r v *
      (of_int (p v) / of_int (q v)) ^ Poly_Mapping.lookup I v =
      of_int (p v ^ Poly_Mapping.lookup I v *
        q v ^ (r v - Poly_Mapping.lookup I v))" if "v < m" for v
    by (rule roth_clear_power) (use qpos[OF that] roth_exponent_boxD(2)[OF box that] in auto)
  have distrib: "(\<Prod>v<m. (of_int (q v)::rat)^r v) *
      (\<Prod>v<m. (of_int (p v) / of_int (q v)::rat) ^ Poly_Mapping.lookup I v) =
      (\<Prod>v<m. (of_int (q v)::rat)^r v *
        (of_int (p v) / of_int (q v)) ^ Poly_Mapping.lookup I v)"
    by (simp add: prod.distrib)
  have prod: "(\<Prod>v<m. (of_int (q v)::rat)^r v *
      (of_int (p v) / of_int (q v)) ^ Poly_Mapping.lookup I v) =
      of_int (\<Prod>v<m. p v ^ Poly_Mapping.lookup I v *
        q v ^ (r v - Poly_Mapping.lookup I v))"
    by (simp add: point)
  have eq: "(\<Prod>v<m. (of_int (q v)::rat) ^ r v) *
      insertion (\<lambda>v. of_int (p v) / of_int (q v))
        (MPoly_Type.monom I (of_int c)) =
      of_int c * ((\<Prod>v<m. (of_int (q v)::rat)^r v) *
        (\<Prod>v<m. (of_int (p v) / of_int (q v)::rat) ^ Poly_Mapping.lookup I v))"
    by (simp add: roth_insertion_monom ipow mult.commute mult.left_commute)
  show ?thesis using eq distrib prod by simp
qed

lemma roth_int_cast_keys:
  fixes P :: "int mpoly"
  shows "Poly_Mapping.keys (mapping_of (replace_coeff (of_int::int \<Rightarrow> rat) P)) =
    Poly_Mapping.keys (mapping_of P)"
by (auto simp: in_keys_iff MPoly_Type.coeff_def[symmetric] coeff_replace_coeff)

lemma roth_int_cast_expansion:
  fixes P :: "int mpoly"
  shows "replace_coeff (of_int::int \<Rightarrow> rat) P =
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P).
      MPoly_Type.monom I (of_int (MPoly_Type.coeff P I)))"
  by (subst roth_sum_monom[of "replace_coeff (of_int::int \<Rightarrow> rat) P"])
    (simp add: roth_int_cast_keys coeff_replace_coeff)

lemma roth_clear_polynomial_evaluation:
  fixes p q :: "nat \<Rightarrow> int" and P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
    and qpos: "\<And>v. v < m \<Longrightarrow> 0 < q v"
  shows "\<exists>z::int. (\<Prod>v<m. (of_int (q v)::rat) ^ r v) *
    insertion (\<lambda>v. of_int (p v) / of_int (q v))
      (replace_coeff of_int P) = of_int z"
proof -
  let ?R = "replace_coeff (of_int::int \<Rightarrow> rat) P"
  let ?S = "Poly_Mapping.keys (mapping_of P)"
  let ?beta = "\<lambda>v. (of_int (p v) / of_int (q v)::rat)"
  let ?D = "(\<Prod>v<m. (of_int (q v)::rat) ^ r v)"
  let ?N = "\<Sum>I\<in>?S. MPoly_Type.coeff P I *
    (\<Prod>v<m. p v ^ Poly_Mapping.lookup I v *
      q v ^ (r v - Poly_Mapping.lookup I v))"
  have fin: "finite ?S" by simp
  have mem: "I \<in> roth_exponent_box m r" if "I \<in> ?S" for I
    using box that by (auto simp: roth_poly_in_box_def)
  have eval: "insertion ?beta ?R =
    (\<Sum>I\<in>?S. insertion ?beta
      (MPoly_Type.monom I (of_int (MPoly_Type.coeff P I))))"
    by (simp add: roth_int_cast_expansion roth_insertion_sum)
  have each: "?D * insertion ?beta
      (MPoly_Type.monom I (of_int (MPoly_Type.coeff P I))) =
      of_int (MPoly_Type.coeff P I *
        (\<Prod>v<m. p v ^ Poly_Mapping.lookup I v *
          q v ^ (r v - Poly_Mapping.lookup I v)))"
    if "I \<in> ?S" for I
    by (rule roth_clear_monom_evaluation[OF mem[OF that] qpos])
  have scale: "?D * insertion ?beta ?R =
    (\<Sum>I\<in>?S. ?D * insertion ?beta
      (MPoly_Type.monom I (of_int (MPoly_Type.coeff P I))))"
    by (simp add: eval sum_distrib_left)
  have eq: "?D * insertion ?beta ?R = of_int ?N"
    using scale by (simp add: each)
  show ?thesis using eq by blast
qed

theorem roth_rational_evaluation_lower:
  fixes p q :: "nat \<Rightarrow> int" and P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
    and qpos: "\<And>v. v < m \<Longrightarrow> 0 < q v"
    and nz: "insertion (\<lambda>v. of_int (p v) / of_int (q v))
      (replace_coeff of_int P) \<noteq> (0::rat)"
  shows "1 / (\<Prod>v<m. (of_int (q v)::rat) ^ r v) \<le>
    abs (insertion (\<lambda>v. of_int (p v) / of_int (q v))
      (replace_coeff of_int P))"
proof -
  let ?D = "(\<Prod>v<m. (of_int (q v)::rat) ^ r v)"
  let ?E = "insertion (\<lambda>v. of_int (p v) / of_int (q v))
      (replace_coeff of_int P)"
  have Dpos: "0 < ?D"
    by (intro prod_pos) (use qpos in auto)
  have ex: "\<exists>z::int. ?D * ?E = of_int z"
    by (rule roth_clear_polynomial_evaluation[where p=p and q=q])
      (use box qpos in auto)
  obtain z::int where z: "?D * ?E = of_int z" using ex by blast
  have zne: "z \<noteq> 0" using Dpos nz z by (metis of_int_0 mult_eq_0_iff not_less_iff_gr_or_eq)
  have "1 \<le> abs (of_int z::rat)" using zne by simp
  moreover have "abs (of_int z::rat) = abs (?D * ?E)"
    using z by simp
  moreover have "abs (?D * ?E) = ?D * abs ?E"
    using Dpos by (simp add: abs_mult)
  ultimately have "1 \<le> ?D * abs ?E" by simp
  then show ?thesis using Dpos by (simp add: divide_le_eq mult.commute)
qed


section \<open>The evaluation bound in terms of rational heights\<close>

theorem roth_rational_evaluation_lower_quotient:
  fixes beta :: "nat \<Rightarrow> rat" and P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "insertion beta (replace_coeff of_int P) \<noteq> (0::rat)"
  shows "1 / (\<Prod>v<m. (of_int (snd (quotient_of (beta v)))::rat) ^ r v) \<le>
    abs (insertion beta (replace_coeff of_int P))"
proof -
  let ?p = "\<lambda>v. fst (quotient_of (beta v))"
  let ?q = "\<lambda>v. snd (quotient_of (beta v))"
  have qpos: "0 < ?q v" for v
    by (rule quotient_of_denom_pos')
  have brep: "beta = (\<lambda>v. of_int (?p v) / of_int (?q v))"
  proof (rule ext)
    fix v
    show "beta v = of_int (?p v) / of_int (?q v)"
      by (cases "quotient_of (beta v)")
        (simp add: quotient_of_div)
  qed
  have raw: "1 / (\<Prod>v<m. (of_int (?q v)::rat) ^ r v) \<le>
    abs (insertion (\<lambda>v. of_int (?p v) / of_int (?q v))
      (replace_coeff of_int P))"
    by (rule roth_rational_evaluation_lower
      [where p="\<lambda>v. fst (quotient_of (beta v))" and
        q="\<lambda>v. snd (quotient_of (beta v))"])
      (use box qpos nz brep in auto)
  show ?thesis using raw brep by simp
qed

lemma roth_quotient_denom_le_height:
  "snd (quotient_of x) \<le> int (roth_rat_height x)"
  using quotient_of_denom_pos'[of x]
  by (simp add: roth_rat_height_def)

theorem roth_rational_evaluation_lower_height:
  fixes beta :: "nat \<Rightarrow> rat" and P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "insertion beta (replace_coeff of_int P) \<noteq> (0::rat)"
  shows "1 / (\<Prod>v<m. (of_nat (roth_rat_height (beta v))::rat) ^ r v) \<le>
    abs (insertion beta (replace_coeff of_int P))"
proof -
  let ?D = "(\<Prod>v<m. (of_int (snd (quotient_of (beta v)))::rat) ^ r v)"
  let ?H = "(\<Prod>v<m. (of_nat (roth_rat_height (beta v))::rat) ^ r v)"
  have Dpos: "0 < ?D"
    by (intro prod_pos) (simp add: quotient_of_denom_pos')
  have Hpos: "0 < ?H"
    by (intro prod_pos) simp
  have point: "(of_int (snd (quotient_of (beta v)))::rat) \<le>
      of_nat (roth_rat_height (beta v))" for v
    using roth_quotient_denom_le_height[of "beta v"] by simp
  have nonneg: "0 \<le> (of_int (snd (quotient_of (beta v)))::rat)" for v
    using quotient_of_denom_pos'[of "beta v"] by simp
  have powpoint: "(of_int (snd (quotient_of (beta v)))::rat) ^ r v \<le>
      (of_nat (roth_rat_height (beta v))::rat) ^ r v" for v
    by (rule power_mono[OF point nonneg])
  have DH: "?D \<le> ?H"
    by (intro prod_mono) (use powpoint nonneg in auto)
  have inv: "1 / ?H \<le> 1 / ?D"
    using Dpos Hpos DH by (simp add: divide_le_eq)
  have lower: "1 / ?D \<le> abs (insertion beta (replace_coeff of_int P))"
    by (rule roth_rational_evaluation_lower_quotient[OF box nz])
  show ?thesis using inv lower by linarith
qed

theorem roth_rational_evaluation_lower_height_real:
  fixes beta :: "nat \<Rightarrow> rat" and P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "insertion beta (replace_coeff of_int P) \<noteq> (0::rat)"
  shows "1 / (\<Prod>v<m. real (roth_rat_height (beta v)) ^ r v) \<le>
    abs (of_rat (insertion beta (replace_coeff of_int P))::real)"
proof -
  note h = roth_rational_evaluation_lower_height[OF box nz]
  have "(of_rat (1 / (\<Prod>v<m.
      (of_nat (roth_rat_height (beta v))::rat) ^ r v))::real) \<le>
    of_rat (abs (insertion beta (replace_coeff of_int P)))"
    using h by (simp add: of_rat_less_eq)
  then show ?thesis
    by (simp add: of_rat_divide of_rat_prod of_rat_power)
qed

lemma roth_height_product_exp:
  fixes beta :: "nat \<Rightarrow> rat"
  shows "1 / (\<Prod>v<m. real (roth_rat_height (beta v)) ^ r v) =
    exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)))"
proof -
  have product: "exp (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v)) =
    (\<Prod>v<m. real (roth_rat_height (beta v)) ^ r v)"
    by (simp add: exp_sum exp_of_nat_mult roth_rat_log_height_def)
  show ?thesis by (simp add: exp_minus product divide_inverse)
qed

end
