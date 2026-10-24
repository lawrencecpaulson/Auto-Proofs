theory Roth_Evaluation_Height
  imports Roth_Evaluation_Sandwich
begin

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

lemma roth_int_index_cast:
  fixes P :: "int mpoly" and beta :: "nat \<Rightarrow> rat"
  shows "roth_index m r beta (replace_coeff (of_int::int \<Rightarrow> rat) P) =
    roth_index m r (\<lambda>v. of_rat (beta v))
      (replace_coeff (of_int::int \<Rightarrow> real) P)"
  by (simp add: roth_index_def roth_int_taylor_cast[symmetric])


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
