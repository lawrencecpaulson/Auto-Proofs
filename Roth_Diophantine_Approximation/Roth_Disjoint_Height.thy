theory Roth_Disjoint_Height
  imports Roth_Rational_Height
begin

section \<open>Coefficient content of disjoint products\<close>

lemma roth_coeffs_eq:
  "coeffs P = {coeff P I | I.
    I \<in> Poly_Mapping.keys (mapping_of P)}"
  by (auto simp: coeffs.rep_eq coeff_def
    Poly_Mapping.range.rep_eq in_keys_iff)

lemma roth_coeffs_nonempty:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0"
  shows "coeffs P \<noteq> {}"
proof
  assume empty: "coeffs P = {}"
  have ki: "I \<notin> Poly_Mapping.keys (mapping_of P)" for I
    using empty by (auto simp: roth_coeffs_eq)
  have keys: "Poly_Mapping.keys (mapping_of P) = {}"
    by (rule set_eqI) (simp add: ki)
  have eq: "mapping_of P = 0" using keys by simp
  have eq0: "mapping_of P = mapping_of (0::int mpoly)"
    using eq by (simp add: zero_mpoly.rep_eq)
  show False using eq0 p by (simp add: mapping_of_inject)
qed

lemma roth_int_coeff_sup_eq_Max:
  fixes P :: "int mpoly"
  assumes p: "P \<noteq> 0"
  shows "roth_int_coeff_sup P =
    Max ((\<lambda>c. nat (abs c)) ` coeffs P)"
proof -
  obtain c where c: "c \<in> coeffs P"
    using roth_coeffs_nonempty[OF p] by blast
  have cnz: "c \<noteq> 0"
    using c by (auto simp: coeffs.rep_eq Poly_Mapping.range.rep_eq)
  have cge: "1 \<le> nat (abs c)" using cnz by simp
  have m: "nat (abs c) \<le>
    Max ((\<lambda>c. nat (abs c)) ` coeffs P)"
    by (rule Max_ge) (use c in auto)
  have le: "1 \<le>
    Max ((\<lambda>c. nat (abs c)) ` coeffs P)"
    using cge m by linarith
  have ne: "((\<lambda>c. nat (abs c)) ` coeffs P) \<noteq> {}"
    using roth_coeffs_nonempty[OF p] by auto
  show ?thesis using le ne
    by (simp add: roth_int_coeff_sup_def Max_insert)
qed

lemma roth_Max_products:
  fixes A B :: "nat set"
  assumes fa: "finite A" and fb: "finite B"
    and na: "A \<noteq> {}" and nb: "B \<noteq> {}"
  shows "Max {a*b | a b. a \<in> A \<and> b \<in> B} = Max A * Max B"
proof (rule Max_eqI)
  have eq: "{a*b | a b. a \<in> A \<and> b \<in> B} =
    (\<lambda>(a,b). a*b) ` (A \<times> B)" by auto
  show "finite {a*b | a b. a \<in> A \<and> b \<in> B}"
    using fa fb by (simp add: eq)
  show "y \<le> Max A * Max B"
    if "y \<in> {a*b | a b. a \<in> A \<and> b \<in> B}" for y
    using that fa fb by (auto intro: mult_le_mono Max_ge)
  show "Max A * Max B \<in>
    {a*b | a b. a \<in> A \<and> b \<in> B}"
    using Max_in[OF fa na] Max_in[OF fb nb] by blast
qed

lemma roth_coeffs_disjoint_mult:
  fixes P Q :: "int mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
  shows "coeffs (P*Q) =
    {a*b | a b. a \<in> coeffs P \<and> b \<in> coeffs Q}"
proof (rule equalityI)
  show "coeffs (P*Q) \<subseteq>
    {a*b | a b. a \<in> coeffs P \<and> b \<in> coeffs Q}"
  proof (rule subsetI)
    fix c assume c: "c \<in> coeffs (P*Q)"
    then obtain K where
      K: "K \<in> Poly_Mapping.keys (mapping_of (P*Q))"
      and cK: "c = coeff (P*Q) K"
      by (auto simp: roth_coeffs_eq)
    obtain I J where
      i: "I \<in> Poly_Mapping.keys (mapping_of P)"
      and j: "J \<in> Poly_Mapping.keys (mapping_of Q)"
      and k: "K = I+J"
      using K Poly_Mapping.keys_mult
        [of "mapping_of P" "mapping_of Q"]
      by (auto simp: times_mpoly.rep_eq)
    have cpq: "coeff (P*Q) K = coeff P I * coeff Q J"
      using k roth_disjoint_prod_coeff[OF disj i j] by simp
    show "c \<in> {a*b | a b.
      a \<in> coeffs P \<and> b \<in> coeffs Q}"
      using cK cpq i j by (auto simp: roth_coeffs_eq)
  qed
  show "{a*b | a b. a \<in> coeffs P \<and> b \<in> coeffs Q}
    \<subseteq> coeffs (P*Q)"
  proof (rule subsetI)
    fix c assume "c \<in> {a*b | a b.
      a \<in> coeffs P \<and> b \<in> coeffs Q}"
    then obtain a b where
      a: "a \<in> coeffs P"
      and b: "b \<in> coeffs Q"
      and c: "c = a*b" by blast
    obtain I where
      i: "I \<in> Poly_Mapping.keys (mapping_of P)"
      and ai: "a = coeff P I"
      using a by (auto simp: roth_coeffs_eq)
    obtain J where
      j: "J \<in> Poly_Mapping.keys (mapping_of Q)"
      and bj: "b = coeff Q J"
      using b by (auto simp: roth_coeffs_eq)
    have nz: "coeff (P*Q) (I+J) \<noteq> 0"
      using roth_disjoint_prod_coeff[OF disj i j] i j
      by (simp add: coeff_def in_keys_iff)
    have k: "I+J \<in> Poly_Mapping.keys (mapping_of (P*Q))"
      using nz by (simp add: coeff_def in_keys_iff)
    have cpq: "coeff (P*Q) (I+J) = c"
      using c ai bj roth_disjoint_prod_coeff[OF disj i j]
      by simp
    show "c \<in> coeffs (P*Q)"
      using k cpq by (auto simp: roth_coeffs_eq)
  qed
qed

lemma roth_Gcd_products:
  fixes A B :: "int set"
  shows "Gcd {a*b | a b. a \<in> A \<and> b \<in> B} = Gcd A * Gcd B"
proof (rule associated_eqI)
  let ?S = "{a*b | a b. a \<in> A \<and> b \<in> B}"
  have Sb: "Gcd ?S dvd a * Gcd B" if "a \<in> A" for a
  proof -
    have h: "Gcd ?S dvd Gcd ((*) a ` B)"
      using that by (auto intro: Gcd_greatest Gcd_dvd)
    show ?thesis using h by (simp add: Gcd_mult dvd_normalize_iff)
  qed
  have h2: "Gcd ?S dvd Gcd ((\<lambda>a. a * Gcd B) ` A)"
    by (rule Gcd_greatest) (auto intro: Sb)
  have eq: "((\<lambda>a. a * Gcd B) ` A) = ((*) (Gcd B) ` A)"
    by auto
  have h3: "Gcd ((\<lambda>a. a * Gcd B) ` A) = Gcd B * Gcd A"
    using eq by (simp add: Gcd_mult normalize_mult)
  have h4: "Gcd ?S dvd Gcd B * Gcd A"
    using h2 h3 by simp
  show "Gcd ?S dvd Gcd A * Gcd B"
    using h4 by (simp only: mult.commute[of "Gcd A" "Gcd B"])
  show "Gcd A * Gcd B dvd Gcd ?S"
    by (rule Gcd_greatest) (auto intro: mult_dvd_mono Gcd_dvd)
  show "normalize (Gcd ?S) = Gcd ?S" by simp
  show "normalize (Gcd A * Gcd B) = Gcd A * Gcd B"
    by (simp add: normalize_mult)
qed

lemma roth_content_disjoint_mult:
  fixes P Q :: "int mpoly"
  assumes "vars P \<inter> vars Q = {}"
  shows "Gcd (coeffs (P*Q)) = Gcd (coeffs P) * Gcd (coeffs Q)"
  by (simp add: roth_coeffs_disjoint_mult[OF assms] roth_Gcd_products)

lemma roth_primitive_disjoint_mult:
  fixes P Q :: "int mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
    and p: "primitive P" and q: "primitive Q"
  shows "primitive (P*Q)"
  using assms
  by (simp add: primitive_def roth_content_disjoint_mult)

lemma roth_int_coeff_sup_disjoint_mult:
  fixes P Q :: "int mpoly"
  assumes disj: "vars P \<inter> vars Q = {}"
    and p: "P \<noteq> 0" and q: "Q \<noteq> 0"
  shows "roth_int_coeff_sup (P*Q) =
    roth_int_coeff_sup P * roth_int_coeff_sup Q"
proof -
  let ?A = "(\<lambda>c. nat (abs c)) ` coeffs P"
  let ?B = "(\<lambda>c. nat (abs c)) ` coeffs Q"
  have eq: "(\<lambda>c. nat (abs c)) ` coeffs (P*Q) =
    {a*b | a b. a \<in> ?A \<and> b \<in> ?B}"
  proof (rule equalityI)
    show "(\<lambda>c. nat (abs c)) ` coeffs (P*Q) \<subseteq>
      {a*b | a b. a \<in> ?A \<and> b \<in> ?B}"
    proof
      fix x assume "x \<in>
        (\<lambda>c. nat (abs c)) ` coeffs (P*Q)"
      then obtain c where c: "c \<in> coeffs (P*Q)"
        and x: "x = nat (abs c)" by blast
      obtain a b where a: "a \<in> coeffs P"
        and b: "b \<in> coeffs Q" and c: "c = a*b"
        using c roth_coeffs_disjoint_mult[OF disj] by blast
      have aa: "nat (abs a) \<in> ?A" using a by blast
      have bb: "nat (abs b) \<in> ?B" using b by blast
      have xeq: "x = nat (abs a) * nat (abs b)"
        using x c by (simp add: nat_abs_mult_distrib)
      show "x \<in> {a*b | a b. a \<in> ?A \<and> b \<in> ?B}"
        using aa bb xeq by blast
    qed
    show "{a*b | a b. a \<in> ?A \<and> b \<in> ?B} \<subseteq>
      (\<lambda>c. nat (abs c)) ` coeffs (P*Q)"
    proof
      fix x assume "x \<in>
        {a*b | a b. a \<in> ?A \<and> b \<in> ?B}"
      then obtain a b where a: "a \<in> ?A"
        and b: "b \<in> ?B" and x: "x = a*b" by blast
      obtain c where c: "c \<in> coeffs P"
        and a: "a = nat (abs c)" using a by blast
      obtain d where d: "d \<in> coeffs Q"
        and b: "b = nat (abs d)" using b by blast
      have cd: "c*d \<in> coeffs (P*Q)"
        using c d roth_coeffs_disjoint_mult[OF disj] by blast
      have xeq: "x = nat (abs (c*d))"
        using x a b by (simp add: nat_abs_mult_distrib)
      show "x \<in> (\<lambda>c. nat (abs c)) ` coeffs (P*Q)"
        using cd xeq by blast
    qed
  qed
  have finA: "finite ?A" and finB: "finite ?B" by auto
  have neA: "?A \<noteq> {}" and neB: "?B \<noteq> {}"
    using roth_coeffs_nonempty[OF p]
      roth_coeffs_nonempty[OF q] by auto
  have pq: "P*Q \<noteq> 0" using p q by auto
  show ?thesis
    using roth_Max_products[OF finA finB neA neB] eq
    by (simp add: roth_int_coeff_sup_eq_Max[OF pq]
      roth_int_coeff_sup_eq_Max[OF p]
      roth_int_coeff_sup_eq_Max[OF q])
qed

end
