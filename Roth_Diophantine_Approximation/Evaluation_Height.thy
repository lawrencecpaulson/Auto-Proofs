theory Evaluation_Height
  imports
    Roth_Lemma
    Auxiliary_Polynomial
begin

section \<open>The auxiliary polynomial with projective height control\<close>

lemma roth_int_coeff_sup_from_pointwise:
  fixes P :: "int mpoly" and B :: int
  assumes B: "1 \<le> B"
    and coeff: "\<And>K. abs (MPoly_Type.coeff P K) \<le> B"
  shows "roth_int_coeff_sup P \<le> nat B"
proof (rule roth_int_coeff_sup_le)
  show "1 \<le> nat B" using B by simp
  fix I
  show "nat (abs (MPoly_Type.coeff P I)) \<le> nat B"
    by (rule nat_mono[OF coeff])
qed

corollary roth_auxiliary_polynomial_monic_sup:
  fixes f :: "int poly" and a :: real
  assumes monic: "Polynomial.lead_coeff f = 1"
    and d: "d = Polynomial.degree f"
    and dpos: "0 < d"
    and root: "poly (map_poly of_int f) a = 0"
    and mpos: "0 < m"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and epos: "0 < eps"
    and elt: "eps < 1"
    and gap: "2 * real d < real m * eps\<^sup>2"
  shows "\<exists>P :: int mpoly.
    P \<noteq> 0 \<and> roth_poly_in_box m r P \<and>
    ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. a) (replace_coeff of_int P) \<and>
    roth_int_coeff_sup P \<le>
      nat (2 * (4 * roth_power_base f) ^ (\<Sum>v<m. r v))"
proof -
  let ?B = "2 * (4 * roth_power_base f) ^ (\<Sum>v<m. r v)"
  obtain P :: "int mpoly" where pn: "P \<noteq> 0"
    and pb: "roth_poly_in_box m r P"
    and pi: "ereal (real m * (1-eps) / 2) \<le>
      roth_index m r (\<lambda>_. a) (replace_coeff of_int P)"
    and pc: "\<forall>K. abs (MPoly_Type.coeff P K) \<le> ?B"
    using roth_auxiliary_polynomial_monic_exp
      [where f=f and a=a and d=d and m=m and r=r and eps=eps,
       OF monic d dpos root mpos rpos epos elt gap] by blast
  have base: "1 \<le> 4 * roth_power_base f"
    using roth_power_base_ge_one[of f] by simp
  have pow: "1 \<le> (4 * roth_power_base f) ^ (\<Sum>v<m. r v)"
    by (rule one_le_power[OF base])
  have Bb: "1 \<le> ?B" using pow by simp
  have hs: "roth_int_coeff_sup P \<le> nat ?B"
    by (rule roth_int_coeff_sup_from_pointwise[OF Bb])
      (use pc in auto)
  show ?thesis using pn pb pi hs by blast
qed


section \<open>Roth bound for an auxiliary polynomial\<close>

lemma roth_int_coeff_sup_log_mono:
  fixes P :: "int mpoly" and B :: nat
  assumes h: "roth_int_coeff_sup P \<le> B"
  shows "ln (real (roth_int_coeff_sup P)) \<le> ln (real B)"
proof (rule ln_mono)
  show "real (roth_int_coeff_sup P) \<le> real B"
    using h by simp
  show "0 < real (roth_int_coeff_sup P)"
    using roth_int_coeff_sup_ge_one[of P] by simp
qed

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

section \<open>Taylor evaluation and the triangle bound\<close>

lemma roth_insertion_Var_diff:
  fixes a b :: "nat \<Rightarrow> 'a::comm_ring_1"
  shows "insertion b (Var v - Const (a v)) = b v - a v"
proof -
  have eq: "Var v - Const (a v) = Var v + Const (-a v)"
    by (simp only: diff_conv_add_uminus roth_Const_uminus[symmetric])
  show ?thesis
    by (simp only: eq insertion_add roth_insertion_Var roth_insertion_Const)
      simp
qed

lemma roth_taylor_evaluation:
  fixes P :: "'a::comm_ring_1 mpoly"
  shows "insertion b P =
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of (roth_translate a P)).
      insertion a (roth_hasse I P) *
        (\<Prod>v\<in>Poly_Mapping.keys I.
          (b v - a v) ^ Poly_Mapping.lookup I v))"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of (roth_translate a P))"
  let ?T = "\<lambda>I. Const (insertion a (roth_hasse I P)) *
      (\<Prod>v\<in>Poly_Mapping.keys I.
        (Var v - Const (a v)) ^ Poly_Mapping.lookup I v)"
  have fin: "finite ?S" by simp
  have expansion: "P = (\<Sum>I\<in>?S. ?T I)"
    by (rule roth_taylor_identity_hasse)
  have eval: "insertion b P = (\<Sum>I\<in>?S. insertion b (?T I))"
    by (subst expansion) (rule roth_insertion_sum_any[OF fin])
  have each: "insertion b (?T I) = insertion a (roth_hasse I P) *
    (\<Prod>v\<in>Poly_Mapping.keys I.
      (b v - a v) ^ Poly_Mapping.lookup I v)" for I
    by (simp add: insertion_mult roth_insertion_prod_any
      roth_insertion_power_any roth_insertion_Var_diff)
  show ?thesis using eval by (simp add: each)
qed

lemma roth_taylor_evaluation_abs:
  fixes P :: "real mpoly"
  shows "abs (insertion b P) \<le>
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of (roth_translate a P)).
      abs (insertion a (roth_hasse I P)) *
        (\<Prod>v\<in>Poly_Mapping.keys I.
          abs (b v - a v) ^ Poly_Mapping.lookup I v))"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of (roth_translate a P))"
  have "abs (insertion b P) = abs
    (\<Sum>I\<in>?S. insertion a (roth_hasse I P) *
      (\<Prod>v\<in>Poly_Mapping.keys I.
        (b v - a v) ^ Poly_Mapping.lookup I v))"
    by (rule arg_cong[where f=abs]) (rule roth_taylor_evaluation)
  also have "... \<le> (\<Sum>I\<in>?S.
      abs (insertion a (roth_hasse I P) *
        (\<Prod>v\<in>Poly_Mapping.keys I.
          (b v - a v) ^ Poly_Mapping.lookup I v)))"
    by (rule sum_abs)
  also have "... = (\<Sum>I\<in>?S.
      abs (insertion a (roth_hasse I P)) *
        (\<Prod>v\<in>Poly_Mapping.keys I.
          abs (b v - a v) ^ Poly_Mapping.lookup I v))"
    by (simp add: abs_mult abs_prod power_abs)
  finally show ?thesis .
qed


section \<open>Bounds from balanced approximation heights\<close>

lemma roth_taylor_support_weight:
  fixes P :: "'a::comm_ring_1 mpoly"
  assumes lower: "ereal theta \<le> roth_index m r a P"
    and mem: "I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))"
  shows "theta \<le> roth_weight m r I"
proof -
  have coeff: "roth_taylor_coeff a I P \<noteq> 0"
    using mem by (simp add: roth_taylor_coeff_key)
  have upper: "roth_index m r a P \<le> ereal (roth_weight m r I)"
    by (rule roth_index_le_coeff[OF coeff])
  have "ereal theta \<le> ereal (roth_weight m r I)"
    by (rule order_trans[OF lower upper])
  then show ?thesis by simp
qed

lemma roth_taylor_uniform_bound:
  fixes P :: "real mpoly" and u :: "nat \<Rightarrow> real"
  assumes B: "0 \<le> B"
    and near: "\<And>v. abs (b v - a v) \<le> u v"
    and coeff: "\<And>I. I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))
      \<Longrightarrow> abs (insertion a (roth_hasse I P)) \<le> B"
  shows "abs (insertion b P) \<le> B *
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of (roth_translate a P)).
      (\<Prod>v\<in>Poly_Mapping.keys I. u v ^ Poly_Mapping.lookup I v))"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of (roth_translate a P))"
  have pow_bound: "abs (b v - a v) ^ n \<le> u v ^ n" for v n
    by (rule power_mono) (use near in auto)
  have prod_bound: "(\<Prod>v\<in>Poly_Mapping.keys I.
        abs (b v - a v) ^ Poly_Mapping.lookup I v) \<le>
      (\<Prod>v\<in>Poly_Mapping.keys I.
        u v ^ Poly_Mapping.lookup I v)" for I
    by (intro prod_mono) (use pow_bound in auto)
  have termbound: "abs (insertion a (roth_hasse I P)) *
      (\<Prod>v\<in>Poly_Mapping.keys I.
        abs (b v - a v) ^ Poly_Mapping.lookup I v) \<le>
      B * (\<Prod>v\<in>Poly_Mapping.keys I.
        u v ^ Poly_Mapping.lookup I v)" if "I \<in> ?S" for I
    by (intro mult_mono coeff[OF that] prod_bound prod_nonneg)
      (use B near in auto)
  have "abs (insertion b P) \<le>
    (\<Sum>I\<in>?S. abs (insertion a (roth_hasse I P)) *
      (\<Prod>v\<in>Poly_Mapping.keys I.
        abs (b v - a v) ^ Poly_Mapping.lookup I v))"
    by (rule roth_taylor_evaluation_abs)
  also have "... \<le> (\<Sum>I\<in>?S. B *
      (\<Prod>v\<in>Poly_Mapping.keys I.
        u v ^ Poly_Mapping.lookup I v))"
    by (intro sum_mono termbound)
  also have "... = B * (\<Sum>I\<in>?S.
      (\<Prod>v\<in>Poly_Mapping.keys I.
        u v ^ Poly_Mapping.lookup I v))"
    by (simp add: sum_distrib_left)
  finally show ?thesis .
qed

lemma roth_weight_height_balance:
  fixes h :: "nat \<Rightarrow> real"
  assumes rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
  shows "L * roth_weight m r I \<le>
    (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)"
proof -
  have local: "L * (real (Poly_Mapping.lookup I v) / real (r v)) \<le>
      real (Poly_Mapping.lookup I v) * h v" if "v < m" for v
  proof -
    have div: "L / real (r v) \<le> h v"
      using rpos[OF that] balance[OF that]
      by (simp add: divide_le_eq mult.commute)
    have h: "real (Poly_Mapping.lookup I v) * (L / real (r v)) \<le>
      real (Poly_Mapping.lookup I v) * h v"
      by (rule mult_left_mono[OF div]) simp
    show ?thesis using h by (simp add: field_simps)
  qed
  have "(\<Sum>v<m. L * (real (Poly_Mapping.lookup I v) / real (r v))) \<le>
    (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)"
  proof (rule sum_mono)
    fix v
    assume "v \<in> {..<m}"
    then have vm: "v < m" by simp
    show "L * (real (Poly_Mapping.lookup I v) / real (r v)) \<le>
      real (Poly_Mapping.lookup I v) * h v"
      by (rule local[OF vm])
  qed
  then show ?thesis
    by (simp add: roth_weight_def sum_distrib_left)
qed

lemma roth_error_product_exp:
  fixes h :: "nat \<Rightarrow> real"
  assumes keys: "Poly_Mapping.keys I \<subseteq> {..<m}"
  shows "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * h v) ^ Poly_Mapping.lookup I v) =
    exp (-kappa * (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v))"
proof -
  have point: "exp (-kappa * h v) ^ Poly_Mapping.lookup I v =
      exp (-kappa * (real (Poly_Mapping.lookup I v) * h v))" for v
    by (simp add: exp_of_nat_mult[symmetric] algebra_simps)
  have prod1: "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * h v) ^ Poly_Mapping.lookup I v) =
    (\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * (real (Poly_Mapping.lookup I v) * h v)))"
    by (intro prod.cong) (use point in auto)
  have prod2: "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * (real (Poly_Mapping.lookup I v) * h v))) =
    exp (\<Sum>v\<in>Poly_Mapping.keys I.
      -kappa * (real (Poly_Mapping.lookup I v) * h v))"
    by (simp add: exp_sum)
  have sum_support: "(\<Sum>v\<in>Poly_Mapping.keys I.
      -kappa * (real (Poly_Mapping.lookup I v) * h v)) =
    (\<Sum>v<m. -kappa * (real (Poly_Mapping.lookup I v) * h v))"
    using keys by (intro sum.mono_neutral_left)
      (auto simp: not_in_keys_iff_lookup_eq_zero)
  have sum_fact: "(\<Sum>v<m. -kappa * (real (Poly_Mapping.lookup I v) * h v)) =
    -kappa * (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)"
    by (simp add: sum_distrib_left)
  show ?thesis using prod1 prod2 sum_support sum_fact by simp
qed

lemma roth_error_product_weight:
  fixes h :: "nat \<Rightarrow> real"
  assumes keys: "Poly_Mapping.keys I \<subseteq> {..<m}"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa"
  shows "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * h v) ^ Poly_Mapping.lookup I v) \<le>
    exp (-kappa * L * roth_weight m r I)"
proof -
  have bw: "L * roth_weight m r I \<le>
    (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)"
    by (rule roth_weight_height_balance[OF rpos balance])
  have mult: "kappa * (L * roth_weight m r I) \<le>
      kappa * (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)"
    by (rule mult_left_mono[OF bw kpos])
  have expl: "exp (-kappa *
      (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v)) \<le>
      exp (-kappa * L * roth_weight m r I)"
    using mult by (simp add: mult.assoc)
  have eq: "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * h v) ^ Poly_Mapping.lookup I v) =
    exp (-kappa * (\<Sum>v<m. real (Poly_Mapping.lookup I v) * h v))"
    by (rule roth_error_product_exp[OF keys])
  show ?thesis using eq expl by simp
qed

lemma roth_error_product_index:
  fixes h :: "nat \<Rightarrow> real"
  assumes keys: "Poly_Mapping.keys I \<subseteq> {..<m}"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and weight: "theta \<le> roth_weight m r I"
  shows "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * h v) ^ Poly_Mapping.lookup I v) \<le>
    exp (-kappa * L * theta)"
proof -
  have e1: "(\<Prod>v\<in>Poly_Mapping.keys I.
      exp (-kappa * h v) ^ Poly_Mapping.lookup I v) \<le>
    exp (-kappa * L * roth_weight m r I)"
    by (rule roth_error_product_weight[OF keys rpos balance kpos])
  have nonneg: "0 \<le> kappa * L" using kpos Lpos by simp
  have mult: "kappa * L * theta \<le>
      kappa * L * roth_weight m r I"
    by (rule mult_left_mono[OF weight nonneg])
  have e2: "exp (-kappa * L * roth_weight m r I) \<le>
      exp (-kappa * L * theta)"
    using mult by simp
  show ?thesis using e1 e2 by (rule order_trans)
qed

theorem roth_taylor_exponential_bound:
  fixes P :: "real mpoly" and h :: "nat \<Rightarrow> real"
  assumes B: "0 \<le> B"
    and keys: "\<And>I. I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))
      \<Longrightarrow> Poly_Mapping.keys I \<subseteq> {..<m}"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and index: "ereal theta \<le> roth_index m r a P"
    and near: "\<And>v. abs (b v - a v) \<le> exp (-kappa * h v)"
    and coeff: "\<And>I. I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))
      \<Longrightarrow> abs (insertion a (roth_hasse I P)) \<le> B"
  shows "abs (insertion b P) \<le>
    B * real (card (Poly_Mapping.keys (mapping_of (roth_translate a P)))) *
      exp (-kappa * L * theta)"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of (roth_translate a P))"
  let ?u = "\<lambda>v. exp (-kappa * h v)"
  let ?E = "exp (-kappa * L * theta)"
  have one: "abs (insertion b P) \<le>
      B * (\<Sum>I\<in>?S.
        (\<Prod>v\<in>Poly_Mapping.keys I.
          ?u v ^ Poly_Mapping.lookup I v))"
    by (rule roth_taylor_uniform_bound[where u="\<lambda>v. exp (-kappa * h v)"])
      (use B near coeff in auto)
  have mon: "(\<Prod>v\<in>Poly_Mapping.keys I.
          ?u v ^ Poly_Mapping.lookup I v) \<le> ?E"
    if "I \<in> ?S" for I
  proof -
    have wt: "theta \<le> roth_weight m r I"
      by (rule roth_taylor_support_weight[OF index that])
    show ?thesis
      by (rule roth_error_product_index[OF keys[OF that] rpos balance
        kpos Lpos wt])
  qed
  have sum_le: "(\<Sum>I\<in>?S.
        (\<Prod>v\<in>Poly_Mapping.keys I.
          ?u v ^ Poly_Mapping.lookup I v)) \<le> real (card ?S) * ?E"
  proof -
    have "(\<Sum>I\<in>?S.
        (\<Prod>v\<in>Poly_Mapping.keys I.
          ?u v ^ Poly_Mapping.lookup I v)) \<le> (\<Sum>I\<in>?S. ?E)"
      by (intro sum_mono) (use mon in auto)
    then show ?thesis by simp
  qed
  have two: "B * (\<Sum>I\<in>?S.
        (\<Prod>v\<in>Poly_Mapping.keys I.
          ?u v ^ Poly_Mapping.lookup I v)) \<le>
      B * (real (card ?S) * ?E)"
    by (rule mult_left_mono[OF sum_le B])
  show ?thesis using one two by (simp add: mult.assoc)
qed


lemma roth_taylor_support_keys_box:
  fixes P :: "real mpoly"
  assumes box: "roth_poly_in_box m r P"
    and mem: "I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))"
  shows "Poly_Mapping.keys I \<subseteq> {..<m}"
proof -
  have tc: "roth_taylor_coeff a I P \<noteq> 0"
    using mem by (simp add: roth_taylor_coeff_key)
  have ev: "insertion a (roth_hasse I P) \<noteq> 0"
    using tc by (simp add: roth_hasse_eval)
  have "roth_hasse I P \<noteq> 0"
    using ev by auto
  then obtain K where ck: "MPoly_Type.coeff (roth_hasse I P) K \<noteq> 0"
    by (metis coeff_all_0)
  have cp: "MPoly_Type.coeff P (K + I) \<noteq> 0"
    by (rule roth_hasse_coeff_support[OF ck])
  have ki: "K + I \<in> roth_exponent_box m r"
    using box cp by (auto simp: roth_poly_in_box_def
      MPoly_Type.coeff_def in_keys_iff)
  have kis: "Poly_Mapping.keys (K + I) \<subseteq> {..<m}"
    by (rule roth_exponent_boxD(1)[OF ki])
  show ?thesis
  proof
    fix v
    assume vi: "v \<in> Poly_Mapping.keys I"
    have iv: "Poly_Mapping.lookup I v \<noteq> 0"
      using vi by (simp add: in_keys_iff)
    have "Poly_Mapping.lookup (K + I) v \<noteq> 0"
      using iv by (simp add: lookup_add)
    then have "v \<in> Poly_Mapping.keys (K + I)"
      by (simp add: in_keys_iff)
    then show "v \<in> {..<m}" using kis by auto
  qed
qed

corollary roth_taylor_exponential_bound_box:
  fixes P :: "real mpoly" and h :: "nat \<Rightarrow> real"
  assumes box: "roth_poly_in_box m r P"
    and B: "0 \<le> B"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and index: "ereal theta \<le> roth_index m r a P"
    and near: "\<And>v. abs (b v - a v) \<le> exp (-kappa * h v)"
    and coeff: "\<And>I. I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))
      \<Longrightarrow> abs (insertion a (roth_hasse I P)) \<le> B"
  shows "abs (insertion b P) \<le>
    B * real (card (Poly_Mapping.keys (mapping_of (roth_translate a P)))) *
      exp (-kappa * L * theta)"
proof (rule roth_taylor_exponential_bound[OF B _ rpos balance kpos
    Lpos index near coeff])
  fix I
  assume "I \<in> Poly_Mapping.keys (mapping_of (roth_translate a P))"
  then show "Poly_Mapping.keys I \<subseteq> {..<m}"
    by (rule roth_taylor_support_keys_box[OF box])
qed

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

lemma roth_real_monom_eval_bound:
  fixes a :: "nat \<Rightarrow> real" and c :: int
  assumes box: "I \<in> roth_exponent_box m r"
  shows "abs (insertion a (MPoly_Type.monom I (of_int c))) \<le>
    real (nat (abs c)) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
proof -
  let ?A = "\<lambda>v. max 1 (abs (a v))"
  have keys: "Poly_Mapping.keys I \<subseteq> {..<m}"
    by (rule roth_exponent_boxD(1)[OF box])
  have point: "abs (a v) ^ Poly_Mapping.lookup I v \<le>
      ?A v ^ r v" if "v \<in> Poly_Mapping.keys I" for v
  proof -
    have vr: "Poly_Mapping.lookup I v \<le> r v"
      by (rule roth_exponent_boxD(2)[OF box]) (use keys that in auto)
    have "abs (a v) ^ Poly_Mapping.lookup I v \<le>
      ?A v ^ Poly_Mapping.lookup I v"
      by (intro power_mono) simp_all
    also have "... \<le> ?A v ^ r v"
      by (rule power_increasing[OF vr]) simp
    finally show ?thesis .
  qed
  have first: "(\<Prod>v\<in>Poly_Mapping.keys I. abs (a v) ^ Poly_Mapping.lookup I v) \<le>
      (\<Prod>v\<in>Poly_Mapping.keys I. ?A v ^ r v)"
    by (intro prod_mono) (use point in auto)
  have second: "(\<Prod>v\<in>Poly_Mapping.keys I. ?A v ^ r v) \<le>
      (\<Prod>v<m. ?A v ^ r v)"
    by (intro prod_mono2) (use keys in auto)
  have eval: "abs (insertion a (MPoly_Type.monom I (of_int c))) =
      real (nat (abs c)) *
        (\<Prod>v\<in>Poly_Mapping.keys I. abs (a v) ^ Poly_Mapping.lookup I v)"
    by (simp add: roth_insertion_monom_any abs_mult abs_prod power_abs)
  show ?thesis using first second eval by (simp add: mult_left_mono)
qed

lemma roth_int_real_cast_expansion:
  fixes P :: "int mpoly"
  shows "replace_coeff (of_int::int \<Rightarrow> real) P =
    (\<Sum>I\<in>Poly_Mapping.keys (mapping_of P).
      MPoly_Type.monom I (of_int (MPoly_Type.coeff P I)))"
  by (subst roth_sum_monom[of "replace_coeff (of_int::int \<Rightarrow> real) P"])
    (simp add: roth_int_cast_keys_real coeff_replace_coeff)

theorem roth_real_poly_eval_bound:
  fixes a :: "nat \<Rightarrow> real" and P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "abs (insertion a (replace_coeff (of_int::int \<Rightarrow> real) P)) \<le>
    real (card (Poly_Mapping.keys (mapping_of P))) *
      real (roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
proof -
  let ?S = "Poly_Mapping.keys (mapping_of P)"
  let ?E = "(\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
  let ?H = "real (roth_int_coeff_sup P)"
  have support: "I \<in> roth_exponent_box m r" if "I \<in> ?S" for I
    using box that by (auto simp: roth_poly_in_box_def)
  have coeff: "real (nat (abs (MPoly_Type.coeff P I))) \<le> ?H" for I
    using roth_int_coeff_sup_coeff[of P I] by simp
  have Epos: "0 \<le> ?E" by (intro prod_nonneg) simp
  have each: "abs (insertion a (MPoly_Type.monom I
      (of_int (MPoly_Type.coeff P I)))) \<le> ?H * ?E"
    if "I \<in> ?S" for I
  proof -
    have b: "abs (insertion a (MPoly_Type.monom I
      (of_int (MPoly_Type.coeff P I)))) \<le>
      real (nat (abs (MPoly_Type.coeff P I))) * ?E"
      by (rule roth_real_monom_eval_bound[OF support[OF that]])
    have c: "real (nat (abs (MPoly_Type.coeff P I))) * ?E \<le> ?H * ?E"
      by (rule mult_right_mono[OF coeff Epos])
    show ?thesis using b c by linarith
  qed
  have eval: "insertion a (replace_coeff (of_int::int \<Rightarrow> real) P) =
      (\<Sum>I\<in>?S. insertion a
        (MPoly_Type.monom I (of_int (MPoly_Type.coeff P I))))"
    by (simp add: roth_int_real_cast_expansion roth_insertion_sum_any)
  have "abs (insertion a (replace_coeff (of_int::int \<Rightarrow> real) P)) \<le>
      (\<Sum>I\<in>?S. abs (insertion a
        (MPoly_Type.monom I (of_int (MPoly_Type.coeff P I)))))"
    by (simp add: eval sum_abs)
  also have "... \<le> (\<Sum>I\<in>?S. ?H * ?E)"
    by (intro sum_mono each)
  also have "... = real (card ?S) * ?H * ?E"
    by (simp add: mult.assoc)
  finally show ?thesis .
qed

lemma roth_hasse_cast_real:
  fixes P :: "int mpoly"
  shows "replace_coeff of_int (roth_hasse J P) =
    (roth_hasse J (replace_coeff of_int P) :: real mpoly)"
  by (simp add: coeff_eq[symmetric] fun_eq_iff
    roth_hasse_coeff_exact coeff_replace_coeff)

theorem roth_hasse_real_eval_bound:
  fixes a :: "nat \<Rightarrow> real" and P :: "int mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "abs (insertion a (roth_hasse J (replace_coeff (of_int::int \<Rightarrow> real) P))) \<le>
    real (card (roth_exponent_box m r)) *
      real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
proof -
  let ?Q = "roth_hasse J P"
  let ?E = "(\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
  have qb: "roth_poly_in_box m r ?Q"
    by (rule roth_hasse_box_int[OF box])
  have eval: "abs (insertion a (roth_hasse J (replace_coeff (of_int::int \<Rightarrow> real) P))) \<le>
      real (card (Poly_Mapping.keys (mapping_of ?Q))) *
        real (roth_int_coeff_sup ?Q) * ?E"
    by (simp only: roth_hasse_cast_real[symmetric])
      (rule roth_real_poly_eval_bound[OF qb])
  have sub: "Poly_Mapping.keys (mapping_of ?Q) \<subseteq> roth_exponent_box m r"
    using qb by (simp add: roth_poly_in_box_def)
  have cards: "card (Poly_Mapping.keys (mapping_of ?Q)) \<le>
      card (roth_exponent_box m r)"
    by (rule card_mono[OF finite_roth_exponent_box sub])
  have hs: "roth_int_coeff_sup ?Q \<le>
      2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P"
    by (rule roth_hasse_coeff_sup[OF box])
  have Epos: "0 \<le> ?E" by (intro prod_nonneg) simp
  have hc: "real (card (Poly_Mapping.keys (mapping_of ?Q))) \<le>
      real (card (roth_exponent_box m r))"
    using cards by simp
  have hh: "real (roth_int_coeff_sup ?Q) \<le>
      real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P)"
    using hs by (metis of_nat_le_iff)
  have prod: "real (card (Poly_Mapping.keys (mapping_of ?Q))) *
      real (roth_int_coeff_sup ?Q) \<le>
    real (card (roth_exponent_box m r)) *
      real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P)"
    by (intro mult_mono hc hh) simp_all
  have "real (card (Poly_Mapping.keys (mapping_of ?Q))) *
      real (roth_int_coeff_sup ?Q) * ?E \<le>
    real (card (roth_exponent_box m r)) *
      real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) * ?E"
    by (rule mult_right_mono[OF prod Epos])
  then show ?thesis using eval by linarith
qed

theorem roth_evaluation_sandwich_height:
  fixes P :: "int mpoly" and beta :: "nat \<Rightarrow> rat"
    and a h :: "nat \<Rightarrow> real"
  assumes box: "roth_poly_in_box m r P"
    and nz: "insertion beta (replace_coeff of_int P) \<noteq> (0::rat)"
    and rpos: "\<And>v. v < m \<Longrightarrow> 0 < r v"
    and balance: "\<And>v. v < m \<Longrightarrow> L \<le> real (r v) * h v"
    and kpos: "0 \<le> kappa" and Lpos: "0 \<le> L"
    and index: "ereal theta \<le> roth_index m r a
      (replace_coeff (of_int::int \<Rightarrow> real) P)"
    and near: "\<And>v. abs (of_rat (beta v) - a v) \<le> exp (-kappa * h v)"
  shows "exp (- (\<Sum>v<m. real (r v) * roth_rat_log_height (beta v))) \<le>
    (real (card (roth_exponent_box m r)) *
      real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v)) *
    real (card (Poly_Mapping.keys
      (mapping_of (roth_translate a (replace_coeff (of_int::int \<Rightarrow> real) P))))) *
      exp (-kappa * L * theta)"
proof -
  let ?B = "real (card (roth_exponent_box m r)) *
      real (2 ^ (\<Sum>v<m. r v) * roth_int_coeff_sup P) *
      (\<Prod>v<m. max 1 (abs (a v)) ^ r v)"
  have Bpos: "0 \<le> ?B"
    by (intro mult_nonneg_nonneg prod_nonneg) simp_all
  have coeff: "abs (insertion a (roth_hasse I
      (replace_coeff (of_int::int \<Rightarrow> real) P))) \<le> ?B" for I
    by (rule roth_hasse_real_eval_bound[OF box])
  show ?thesis
    by (rule roth_evaluation_sandwich[OF box nz Bpos rpos balance
      kpos Lpos index near]) (use coeff in auto)
qed


lemma roth_int_taylor_cast:
  fixes P :: "int mpoly" and beta :: "nat \<Rightarrow> rat"
  shows "(of_rat (roth_taylor_coeff beta I
      (replace_coeff (of_int::int \<Rightarrow> rat) P))::real) =
    roth_taylor_coeff (\<lambda>v. of_rat (beta v)) I
      (replace_coeff (of_int::int \<Rightarrow> real) P)"
  by (simp add: roth_hasse_eval[symmetric] roth_hasse_cast[symmetric]
    roth_hasse_cast_real[symmetric] roth_integer_evaluation_cast)

lemma roth_real_taylor_index_box:
  fixes P :: "real mpoly"
  assumes box: "roth_poly_in_box m r P"
    and tc: "roth_taylor_coeff a I P \<noteq> 0"
  shows "I \<in> roth_exponent_box m r"
proof -
  have hne: "roth_hasse I P \<noteq> 0"
    using tc by (auto simp: roth_hasse_eval[symmetric])
  obtain K where ck: "MPoly_Type.coeff (roth_hasse I P) K \<noteq> 0"
    using hne coeff_all_0 by blast
  have cp: "MPoly_Type.coeff P (K+I) \<noteq> 0"
    by (rule roth_hasse_coeff_support[OF ck])
  have ki: "K+I \<in> roth_exponent_box m r"
    using box cp by (auto simp: roth_poly_in_box_def MPoly_Type.coeff_def in_keys_iff)
  show ?thesis
  proof (rule roth_exponent_boxI)
    have sub: "Poly_Mapping.keys I \<subseteq> Poly_Mapping.keys (K+I)"
      by (auto simp: in_keys_iff lookup_add)
    show "Poly_Mapping.keys I \<subseteq> {..<m}"
      using sub roth_exponent_boxD(1)[OF ki] by blast
    fix v assume vm: "v<m"
    have "Poly_Mapping.lookup I v \<le> Poly_Mapping.lookup (K+I) v"
      by (simp add: lookup_add)
    also have "... \<le> r v"
      by (rule roth_exponent_boxD(2)[OF ki vm])
    finally show "Poly_Mapping.lookup I v \<le> r v" .
  qed
qed



lemma roth_real_taylor_card_bound:
  fixes P :: "real mpoly"
  assumes box: "roth_poly_in_box m r P"
  shows "card (Poly_Mapping.keys (mapping_of (roth_translate a P))) \<le>
    card (roth_exponent_box m r)"
proof (rule card_mono[OF finite_roth_exponent_box])
  show "Poly_Mapping.keys (mapping_of (roth_translate a P)) \<subseteq>
      roth_exponent_box m r"
    using box by (auto simp: roth_taylor_coeff_key[symmetric]
      intro: roth_real_taylor_index_box)
qed


lemma roth_low_index_derivative:
  fixes P :: "int mpoly" and beta :: "nat \<Rightarrow> rat"
  assumes low: "roth_index m r beta (replace_coeff (of_int::int \<Rightarrow> rat) P) < ereal t"
  obtains J where "roth_weight m r J < t"
    "insertion beta (replace_coeff (of_int::int \<Rightarrow> rat) (roth_hasse J P)) \<noteq> 0"
proof -
  let ?Q = "replace_coeff (of_int::int \<Rightarrow> rat) P"
  have qnz: "?Q \<noteq> 0"
    using low by auto
  obtain J where c: "roth_taylor_coeff beta J ?Q \<noteq> 0"
    and idx: "roth_index m r beta ?Q = ereal (roth_weight m r J)"
    by (rule roth_index_attained[OF qnz])
  have wt: "roth_weight m r J < t" using low idx by simp
  have nz: "insertion beta (replace_coeff (of_int::int \<Rightarrow> rat) (roth_hasse J P)) \<noteq> 0"
    using c by (simp add: roth_hasse_eval[symmetric] roth_hasse_cast[symmetric])
  show thesis by (rule that[OF wt nz])
qed


lemma roth_index_hasse_from_lower:
  fixes P :: "real mpoly"
  assumes idx: "ereal t \<le> roth_index m r a P"
  shows "ereal (t - roth_weight m r J) \<le>
    roth_index m r a (roth_hasse J P)"
proof -
  have le: "ereal t \<le> ereal (roth_weight m r J) +
      roth_index m r a (roth_hasse J P)"
    using idx roth_index_hasse_add[of m r a P J] by (rule order_trans)
  have e: "ereal (t - roth_weight m r J) =
    ereal t - ereal (roth_weight m r J)" by simp
  have eq: "ereal t - ereal (roth_weight m r J) \<le>
      roth_index m r a (roth_hasse J P) \<longleftrightarrow>
    ereal t \<le> roth_index m r a (roth_hasse J P) +
      ereal (roth_weight m r J)"
    by (rule ereal_minus_le) simp
  have le2: "ereal t \<le> roth_index m r a (roth_hasse J P) +
      ereal (roth_weight m r J)"
    using le by (simp only: add.commute)
  show ?thesis using le2 eq e by metis
qed

end
