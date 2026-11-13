theory Resultant_Multiplicity
  imports Bivariate_Polynomial Factor_Algebraic_Polynomial.Multivariate_Resultant
begin

text \<open>Green, Appendix A ("Resultants"), especially Lemma A.1 and
  the degree bound preceding it: the elimination polynomial is the resultant
  of a bivariate polynomial and its first-variable derivative. Section 3
  uses these facts in the proof of Lemma 3.1.\<close>

lemma irreducible_resultant_pderiv_nonzero:
  fixes p :: "complex poly poly"
  assumes irr: "irreducible p" and pos: "0 < degree p"
  shows "resultant p (pderiv p) \<noteq> 0"
proof
  assume zero: "resultant p (pderiv p) = 0"
  have noncop: "\<not> coprime p (pderiv p)"
    by (rule resultant_zero_imp_common_factor[OF disjI1[OF pos] zero])
  have prime: "prime_elem p"
    by (rule irreducible_imp_prime_elem[OF irr])
  have "\<not> p dvd pderiv p" using pos by simp
  then have "coprime p (pderiv p)"
    using prime by (simp add: prime_elem_imp_coprime)
  with noncop show False by contradiction
qed

definition first_resultant :: "complex mpoly \<Rightarrow> complex mpoly" where
  "first_resultant F =
    resultant (mpoly_to_mpoly_poly 0 F) (pderiv (mpoly_to_mpoly_poly 0 F))"

lemma nat_scalar_mpoly:
  "(1 + of_nat k :: complex mpoly) = Const (1 + of_nat k)"
  by (metis of_nat_mpoly_eq mpoly_Const_1 mpoly_Const_add)

lemma vars_first_resultant:
  assumes "bivariate F"
  shows "vars (first_resultant F) \<subseteq> {1}"
proof -
  let ?p = "mpoly_to_mpoly_poly 0 F"
  have c: "\<And>k. vars (coeff ?p k) \<subseteq> {1}"
    using bivariate_coeff_first[OF assms] .
  have scalar: "vars (1 + of_nat k :: complex mpoly) = {}" for k
    by (simp add: nat_scalar_mpoly vars_empty_iff)
  have d: "\<And>k. vars (coeff (pderiv ?p) k) \<subseteq> {1}"
  proof -
    fix k
    have "vars ((1 + of_nat k) * coeff ?p (Suc k)) \<subseteq>
      vars (1 + of_nat k :: complex mpoly) \<union> vars (coeff ?p (Suc k))"
      by (rule vars_mult)
    also have "... \<subseteq> {1}" using scalar[of k] c[of "Suc k"] by auto
    finally show "vars (coeff (pderiv ?p) k) \<subseteq> {1}"
      by (simp add: coeff_pderiv)
  qed
  show ?thesis
    unfolding first_resultant_def
    using vars_resultant[of ?p "pderiv ?p"] c d by blast
qed

definition first_resultant_poly :: "complex mpoly \<Rightarrow> complex poly" where
  "first_resultant_poly F = mpoly_to_poly 1 (first_resultant F)"

lemma poly_first_resultant_poly:
  assumes "bivariate F"
  shows "poly (first_resultant_poly F) a = insertion (\<lambda>_. a) (first_resultant F)"
  using poly_eq_insertion[OF vars_first_resultant[OF assms]]
  by (simp add: first_resultant_poly_def)

lemma first_resultant_poly_nonzero_iff:
  assumes "bivariate F"
  shows "first_resultant_poly F \<noteq> 0 \<longleftrightarrow> first_resultant F \<noteq> 0"
proof
  assume "first_resultant_poly F \<noteq> 0"
  show "first_resultant F \<noteq> 0"
    using \<open>first_resultant_poly F \<noteq> 0\<close> mpoly_to_poly_zero[of 1]
    by (metis first_resultant_poly_def)
next
  assume "first_resultant F \<noteq> 0"
  then show "first_resultant_poly F \<noteq> 0"
    using pure_second_polynomial_nonzero[OF vars_first_resultant[OF assms]]
    by (simp add: first_resultant_poly_def)
qed

lemma first_resultant_specialize:
  assumes bv: "bivariate F"
    and deg: "degree (specialize_second a F) = MPoly_Type.degree F 0"
  shows "poly (first_resultant_poly F) a =
    resultant (specialize_second a F) (pderiv (specialize_second a F))"
proof -
  let ?p = "mpoly_to_mpoly_poly 0 F"
  let ?h = "insertion (\<lambda>_. a)"
  interpret h: idom_hom ?h by (unfold_locales; simp)
  have eq: "map_poly ?h ?p = specialize_second a F"
    by (simp add: partial_insertion_def)
  have der: "map_poly ?h (pderiv ?p) = pderiv (specialize_second a F)"
    using specialize_first_pderiv[of "\<lambda>_. a" 0 F] by simp
  have dp: "degree (map_poly ?h ?p) = degree ?p"
    using deg by (simp add: eq)
  have dd: "degree (map_poly ?h (pderiv ?p)) = degree (pderiv ?p)"
    by (simp add: der eq[symmetric] dp degree_pderiv)
  have "resultant (map_poly ?h ?p) (map_poly ?h (pderiv ?p)) =
    ?h (resultant ?p (pderiv ?p))"
    by (rule h.resultant_map_poly[OF dp dd])
  then show ?thesis
    using poly_first_resultant_poly[OF bv, of a]
    by (simp add: first_resultant_def eq der)
qed

lemma first_resultant_specialize_fixed_size:
  assumes "bivariate F"
  shows "poly (first_resultant_poly F) a =
    det (sylvester_mat_sub (MPoly_Type.degree F 0)
      (degree (pderiv (mpoly_to_mpoly_poly 0 F)))
      (specialize_second a F) (pderiv (specialize_second a F)))"
proof -
  let ?p = "mpoly_to_mpoly_poly 0 F"
  let ?h = "insertion (\<lambda>_. a)"
  interpret h: comm_ring_hom ?h by (rule comm_ring_hom_insertion)
  have eq: "map_poly ?h ?p = specialize_second a F"
    by (simp add: partial_insertion_def)
  have der: "map_poly ?h (pderiv ?p) = pderiv (specialize_second a F)"
    using specialize_first_pderiv[of "\<lambda>_. a" 0 F] by simp
  have "poly (first_resultant_poly F) a = ?h (resultant ?p (pderiv ?p))"
    using poly_first_resultant_poly[OF assms, of a]
    by (simp add: first_resultant_def)
  also have "... = ?h (resultant_sub (degree ?p) (degree (pderiv ?p))
      ?p (pderiv ?p))"
    by (simp add: resultant_def sylvester_mat_def resultant_sub_def)
  also have "... = resultant_sub (degree ?p) (degree (pderiv ?p))
      (map_poly ?h ?p) (map_poly ?h (pderiv ?p))"
    by (rule h.resultant_sub_map_poly)
  finally show ?thesis by (simp add: resultant_sub_def eq der)
qed

lemma first_resultant_specialize_matrix:
  assumes "bivariate F" "0 < MPoly_Type.degree F 0"
  shows "poly (first_resultant_poly F) a =
    det (sylvester_mat_sub (MPoly_Type.degree F 0)
      (MPoly_Type.degree F 0 - 1)
      (specialize_second a F) (pderiv (specialize_second a F)))"
  using first_resultant_specialize_fixed_size[OF assms(1), of a]
    degree_pderiv[of "mpoly_to_mpoly_poly 0 F"] assms(2)
  by simp

lemma first_resultant_degree_preserved_somewhere:
  assumes bv: "bivariate F" and pos: "0 < MPoly_Type.degree F 0"
  shows "\<exists>a. degree (specialize_second a F) = MPoly_Type.degree F 0"
proof -
  let ?p = "mpoly_to_mpoly_poly 0 F"
  let ?d = "MPoly_Type.degree F 0"
  let ?c = "coeff ?p ?d"
  have cnz: "?c \<noteq> 0"
  proof -
    have pnz: "?p \<noteq> 0" using pos by auto
    have "coeff ?p (degree ?p) \<noteq> 0" using pnz by (simp only: leading_coeff_0_iff; simp)
    then show ?thesis by simp
  qed
  have cv: "vars ?c \<subseteq> {1}"
    by (rule bivariate_coeff_first[OF bv])
  have pnz: "mpoly_to_poly 1 ?c \<noteq> 0"
    by (rule pure_second_polynomial_nonzero[OF cv cnz])
  then obtain a where anz: "poly (mpoly_to_poly 1 ?c) a \<noteq> 0"
    using poly_all_0_iff_0 by blast
  have c: "coeff (specialize_second a F) ?d \<noteq> 0"
    using anz poly_eq_insertion[OF cv, of a]
    by simp
  have hi: "degree (specialize_second a F) \<le> ?d"
    using degree_specialize_first[of "\<lambda>_. a" 0 F] by simp
  have lo: "?d \<le> degree (specialize_second a F)"
    using c by (simp add: le_degree)
  show ?thesis using hi lo by (intro exI[of _ a]) simp
qed

lemma first_resultant_nonzero_of_coprime_specialization:
  assumes bv: "bivariate F"
    and pos: "0 < MPoly_Type.degree F 0"
    and deg: "degree (specialize_second a F) = MPoly_Type.degree F 0"
    and cop: "coprime (specialize_second a F) (pderiv (specialize_second a F))"
  shows "first_resultant_poly F \<noteq> 0"
proof
  assume z: "first_resultant_poly F = 0"
  have rz: "resultant (specialize_second a F)
      (pderiv (specialize_second a F)) = 0"
    using z first_resultant_specialize[OF bv deg] by simp
  have "\<not> coprime (specialize_second a F) (pderiv (specialize_second a F))"
    by (rule resultant_zero_imp_common_factor[OF disjI1, OF _ rz])
      (use deg pos in simp)
  with cop show False by contradiction
qed

lemma eval_map_pderiv:
  fixes P :: "complex poly poly"
  shows "map_poly (\<lambda>q. poly q a) (pderiv P) =
    pderiv (map_poly (\<lambda>q. poly q a) P)"
  by (rule poly_eqI) (simp add: coeff_pderiv coeff_map_poly)

lemma first_resultant_poly_nested:
  assumes bv: "bivariate F"
  shows "first_resultant_poly F =
    resultant (bivariate_as_poly_poly F) (pderiv (bivariate_as_poly_poly F))"
proof (rule poly_ext)
  fix a
  let ?P = "bivariate_as_poly_poly F"
  let ?h = "\<lambda>q::complex poly. poly q a"
  have H: "comm_ring_hom ?h" by (unfold_locales; simp)
  have sp: "map_poly ?h ?P = specialize_second a F"
    by (rule specialize_bivariate_as_poly_poly[OF bv])
  have der: "map_poly ?h (pderiv ?P) = pderiv (specialize_second a F)"
    using eval_map_pderiv[of a ?P] sp by simp
  have pd: "degree ?P = MPoly_Type.degree F 0"
    by (rule degree_bivariate_as_poly_poly[OF bv])
  have dd: "degree (pderiv ?P) = degree (pderiv (mpoly_to_mpoly_poly 0 F))"
    using pd by (simp add: degree_pderiv)
  have "poly (resultant ?P (pderiv ?P)) a =
      resultant_sub (degree ?P) (degree (pderiv ?P))
        (map_poly ?h ?P) (map_poly ?h (pderiv ?P))"
    by (simp add: resultant_sub comm_ring_hom.resultant_sub_map_poly[OF H])
  also have "... = poly (first_resultant_poly F) a"
    using first_resultant_specialize_fixed_size[OF bv, of a]
    by (simp add: resultant_sub_def sp der pd dd)
  finally show "poly (first_resultant_poly F) a =
    poly (resultant ?P (pderiv ?P)) a" by simp
qed

lemma first_resultant_nonzero_irreducible:
  assumes bv: "bivariate F" and irr: "irreducible F"
    and pos: "0 < MPoly_Type.degree F 0"
  shows "first_resultant_poly F \<noteq> 0"
proof -
  have pi: "irreducible (bivariate_as_poly_poly F)"
    by (rule bivariate_as_poly_poly_irreducible[OF bv irr])
  have pd: "0 < degree (bivariate_as_poly_poly F)"
    using degree_bivariate_as_poly_poly[OF bv] pos by simp
  show ?thesis
    using irreducible_resultant_pderiv_nonzero[OF pi pd]
      first_resultant_poly_nested[OF bv] by simp
qed

lemma first_resultant_nonzero_degree_one:
  assumes bv: "bivariate F" and d: "MPoly_Type.degree F 0 = 1"
  shows "first_resultant_poly F \<noteq> 0"
proof -
  obtain a where deg: "degree (specialize_second a F) = 1"
    using first_resultant_degree_preserved_somewhere[OF bv] d by auto
  let ?f = "specialize_second a F"
  have nz: "pderiv ?f \<noteq> 0"
    using deg by (simp add: pderiv_eq_0_iff)
  have "is_unit (pderiv ?f)"
    using deg nz by (simp add: degree_pderiv is_unit_poly_iff)
  then have "coprime ?f (pderiv ?f)"
    by (simp add: is_unit_right_imp_coprime)
  then show ?thesis
    using first_resultant_nonzero_of_coprime_specialization[OF bv, of a] d deg by auto
qed

lemma first_resultant_multiplicity_degree_one:
  assumes bv: "bivariate F" and irr: "irreducible F"
    and d: "MPoly_Type.degree F 0 = 1"
  shows "Polynomial.order x (specialize_second a F) \<le>
    1 + Polynomial.order a (first_resultant_poly F)"
proof -
  have nz: "specialize_second a F \<noteq> 0"
    by (rule irreducible_specialize_second_nonzero[OF bv irr])
      (use d in simp)
  have hi: "degree (specialize_second a F) \<le> 1"
    using degree_specialize_first[of "\<lambda>_. a" 0 F] d by simp
  have "Polynomial.order x (specialize_second a F) \<le> 1"
    using order_degree[OF nz, of x] hi by linarith
  then show ?thesis by simp
qed

lemma root_power_dvd_sylvester_image:
  fixes f h k :: "complex poly"
  assumes nz: "f \<noteq> 0" and mult: "0 < Polynomial.order x f"
  shows "[:-x, 1:] ^ (Polynomial.order x f - 1) dvd
    h * f + k * pderiv f"
proof -
  let ?m = "Polynomial.order x f"
  let ?L = "[:-x, 1:] ^ (?m - 1)"
  have root: "poly f x = 0" using nz mult by (simp add: order_root)
  have der: "?m = Suc (Polynomial.order x (pderiv f))"
    by (rule order_pderiv[OF nz root])
  have fd: "?L dvd f"
    by (rule power_le_dvd[OF order_1]) simp
  have dd: "?L dvd pderiv f"
    using order_1[of x "pderiv f"] der by simp
  have "?L dvd h * f" using fd by (metis dvd_mult2 mult.commute)
  moreover have "?L dvd k * pderiv f" using dd by (metis dvd_mult2 mult.commute)
  ultimately show ?thesis by simp
qed

lemma sylvester_det_degree_drop:
  fixes f :: "complex poly"
  assumes pos: "0 < d" and drop: "degree f < d"
  shows "det (sylvester_mat_sub d (d - 1) f (pderiv f)) = 0"
proof -
  let ?n = "d - 1"
  let ?N = "d + ?n"
  let ?A = "sylvester_mat_sub d ?n f (pderiv f)"
  have fc: "coeff f d = 0" using drop by (simp add: coeff_eq_0)
  have dc: "coeff (pderiv f) ?n = 0"
    using pos fc by (cases d) (simp_all add: coeff_pderiv)
  have Npos: "0 < ?N" using pos by simp
  have col0: "?A $$ (i,0) = 0" if "i < ?N" for i
  proof (cases "i < ?n")
    case True
    then show ?thesis using that fc
      by (cases i) (auto simp: sylvester_mat_sub_def)
  next
    case False
    then have "i = ?n \<or> ?n < i" by arith
    then show ?thesis using that dc
      by (auto simp: sylvester_mat_sub_def)
  qed
  have mat: "?A \<in> carrier_mat ?N ?N"
    by (rule sylvester_mat_sub_carrier)
  have "det ?A = (\<Sum>p | p permutes {..< ?N}.
      signof p * (\<Prod>j<?N. ?A $$ (p j,j)))"
    using det_col[OF mat] by (simp add: atLeast0LessThan)
  also have "... = 0"
  proof (rule sum.neutral, intro ballI)
    fix p
    assume p: "p \<in> {p. p permutes {..< ?N}}"
    have p0: "p 0 < ?N"
      using p Npos by (metis lessThan_iff mem_Collect_eq permutes_in_image)
    have "(\<Prod>j<?N. ?A $$ (p j,j)) = 0"
      by (rule prod_zero) (use Npos col0[OF p0] in auto)
    then show "signof p * (\<Prod>j<?N. ?A $$ (p j,j)) = 0" by simp
  qed
  finally show ?thesis .
qed

lemma first_resultant_double_root:
  assumes bv: "bivariate F"
    and deg: "degree (specialize_second a F) = MPoly_Type.degree F 0"
    and nz: "specialize_second a F \<noteq> 0"
    and mult: "2 \<le> Polynomial.order x (specialize_second a F)"
  shows "poly (first_resultant_poly F) a = 0"
proof -
  let ?f = "specialize_second a F"
  have root: "poly ?f x = 0"
    using mult by (auto simp: order_root)
  have dpos: "degree ?f > 0"
    using mult order_degree[OF nz, of x] by linarith
  have d2: "2 \<le> degree ?f"
    using mult order_degree[OF nz, of x] by linarith
  have dro: "0 < Polynomial.order x (pderiv ?f)"
    using order_pderiv[OF nz root] mult by linarith
  have dnz: "pderiv ?f \<noteq> 0"
  proof
    assume z: "pderiv ?f = 0"
    have "degree (pderiv ?f) = degree ?f - 1" by (rule degree_pderiv)
    with d2 z show False by simp
  qed
  have rootd: "poly (pderiv ?f) x = 0"
    using dro dnz by (simp add: order_gt_0_iff)
  have "resultant ?f (pderiv ?f) = 0"
    by (rule resultant_zero[OF disjI1[OF dpos] root rootd])
  then show ?thesis using first_resultant_specialize[OF bv deg] by simp
qed

lemma first_resultant_degree_drop:
  assumes bv: "bivariate F"
    and pos: "0 < MPoly_Type.degree F 0"
    and drop: "degree (specialize_second a F) < MPoly_Type.degree F 0"
  shows "poly (first_resultant_poly F) a = 0"
proof -
  have "det (sylvester_mat_sub (MPoly_Type.degree F 0)
          (MPoly_Type.degree F 0 - 1)
          (specialize_second a F) (pderiv (specialize_second a F))) = 0"
    by (rule sylvester_det_degree_drop[OF pos drop])
  then show ?thesis using first_resultant_specialize_matrix[OF bv pos, of a] by simp
qed

lemma first_resultant_double_root_any:
  assumes bv: "bivariate F"
    and pos: "0 < MPoly_Type.degree F 0"
    and nz: "specialize_second a F \<noteq> 0"
    and mult: "2 \<le> Polynomial.order x (specialize_second a F)"
  shows "poly (first_resultant_poly F) a = 0"
proof (cases "degree (specialize_second a F) = MPoly_Type.degree F 0")
  case True
  then show ?thesis by (rule first_resultant_double_root[OF bv _ nz mult])
next
  case False
  have drop: "degree (specialize_second a F) < MPoly_Type.degree F 0"
    using degree_specialize_first[of "\<lambda>_. a" 0 F] False by simp
  show ?thesis by (rule first_resultant_degree_drop[OF bv pos drop])
qed


lemma first_resultant_nonroot_fibre_simple:
  assumes bv: "bivariate F"
    and pos: "0 < MPoly_Type.degree F 0"
    and nz: "specialize_second a F \<noteq> 0"
    and rn: "poly (first_resultant_poly F) a \<noteq> 0"
  shows "degree (specialize_second a F) = MPoly_Type.degree F 0"
    and "Polynomial.order x (specialize_second a F) \<le> 1"
proof -
  have hi: "degree (specialize_second a F) \<le> MPoly_Type.degree F 0"
    using degree_specialize_first[of "\<lambda>_. a" 0 F] by simp
  have "\<not> degree (specialize_second a F) < MPoly_Type.degree F 0"
    using first_resultant_degree_drop[OF bv pos] rn by blast
  with hi show "degree (specialize_second a F) = MPoly_Type.degree F 0"
    by simp
  show "Polynomial.order x (specialize_second a F) \<le> 1"
  proof (rule ccontr)
    assume "\<not> Polynomial.order x (specialize_second a F) \<le> 1"
    then have "2 \<le> Polynomial.order x (specialize_second a F)" by simp
    then have "poly (first_resultant_poly F) a = 0"
      by (rule first_resultant_double_root_any[OF bv pos nz])
    with rn show False by simp
  qed
qed

lemma first_resultant_multiplicity_degree_le_two:
  assumes bv: "bivariate F" and pos: "0 < MPoly_Type.degree F 0"
    and small: "MPoly_Type.degree F 0 \<le> 2"
    and nz: "specialize_second a F \<noteq> 0"
    and rnz: "first_resultant_poly F \<noteq> 0"
  shows "Polynomial.order x (specialize_second a F) \<le>
    1 + Polynomial.order a (first_resultant_poly F)"
proof -
  have deg: "degree (specialize_second a F) \<le> 2"
    using degree_specialize_first[of "\<lambda>_. a" 0 F] small by simp
  have ord: "Polynomial.order x (specialize_second a F) \<le> 2"
    using order_degree[OF nz, of x] deg by linarith
  show ?thesis
  proof (cases "Polynomial.order x (specialize_second a F) \<le> 1")
    case True
    then show ?thesis by simp
  next
    case False
    then have mult: "2 \<le> Polynomial.order x (specialize_second a F)"
      by simp
    have root: "poly (first_resultant_poly F) a = 0"
      by (rule first_resultant_double_root_any[OF bv pos nz mult])
    have "0 < Polynomial.order a (first_resultant_poly F)"
      using rnz root by (simp add: order_gt_0_iff)
    with ord show ?thesis by linarith
  qed
qed

lemma degree_coeff_first_le:
  "MPoly_Type.degree (coeff (mpoly_to_mpoly_poly 0 F) k) 1
    \<le> MPoly_Type.degree F 1"
proof (rule degree_leI)
  fix m :: "(nat, nat) poly_mapping"
  assume m: "Poly_Mapping.lookup m 1 > MPoly_Type.degree F 1"
  have big: "Poly_Mapping.lookup (m + Poly_Mapping.single 0 k) 1 > MPoly_Type.degree F 1"
    using m by (simp add: Poly_Mapping.lookup_add lookup_single_not_eq)
  show "MPoly_Type.coeff (coeff (mpoly_to_mpoly_poly 0 F) k) m = 0"
    using coeff_gt_degree_eq_0[OF big]
    by (simp add: coeff_coeff_mpoly_to_mpoly_poly when_def)
qed

lemma mpoly_degree_add_le:
  fixes P Q :: "complex mpoly"
  shows "MPoly_Type.degree (P + Q) i \<le>
    max (MPoly_Type.degree P i) (MPoly_Type.degree Q i)"
  by (metis degree_add_le_max degree_mpoly_to_mpoly_poly mpoly_to_mpoly_poly_add)

lemma mpoly_degree_mult_le:
  fixes P Q :: "complex mpoly"
  shows "MPoly_Type.degree (P * Q) i \<le>
    MPoly_Type.degree P i + MPoly_Type.degree Q i"
  by (metis degree_mult_le degree_mpoly_to_mpoly_poly mpoly_to_mpoly_poly_mult)

lemma mpoly_degree_sum_le:
  fixes f :: "'a \<Rightarrow> complex mpoly"
  assumes "finite S" "\<And>x. x \<in> S \<Longrightarrow> MPoly_Type.degree (f x) i \<le> D"
  shows "MPoly_Type.degree (\<Sum>x\<in>S. f x) i \<le> D"
  using assms by (induction S rule: finite_induct)
    (auto intro: order.trans[OF mpoly_degree_add_le])

lemma mpoly_degree_prod_le:
  fixes f :: "'a \<Rightarrow> complex mpoly"
  assumes "finite S"
  shows "MPoly_Type.degree (\<Prod>x\<in>S. f x) i \<le>
    (\<Sum>x\<in>S. MPoly_Type.degree (f x) i)"
  using assms by (induction S rule: finite_induct)
    (auto intro: order.trans[OF mpoly_degree_mult_le])

lemma mpoly_degree_det_row_le:
  fixes A :: "complex mpoly mat"
  assumes mat: "A \<in> carrier_mat n n"
    and entries: "\<And>j k. j < n \<Longrightarrow> k < n \<Longrightarrow>
      MPoly_Type.degree (A $$ (j,k)) v \<le> D j"
  shows "MPoly_Type.degree (det A) v \<le> (\<Sum>j<n. D j)"
proof -
  let ?P = "{p. p permutes {0..<n}}"
  have finite: "finite ?P" using finite_permutations by blast
  have bound: "MPoly_Type.degree (signof p * (\<Prod>j<n. A $$ (j,p j))) v
      \<le> (\<Sum>j<n. D j)" if "p \<in> ?P" for p
  proof -
    have pj: "p j < n" if "j < n" for j
      using that \<open>p \<in> ?P\<close> by (simp add: permutes_in_image)
    have prod: "MPoly_Type.degree (\<Prod>j<n. A $$ (j,p j)) v
        \<le> (\<Sum>j<n. D j)"
    proof -
      have "MPoly_Type.degree (\<Prod>j<n. A $$ (j,p j)) v \<le>
          (\<Sum>j<n. MPoly_Type.degree (A $$ (j,p j)) v)"
        by (rule mpoly_degree_prod_le) simp
      also have "... \<le> (\<Sum>j<n. D j)"
        by (rule sum_mono) (auto intro: entries pj)
      finally show ?thesis .
    qed
    have minus: "MPoly_Type.degree (-1 :: complex mpoly) v = 0"
      using degree_mpoly_to_mpoly_poly[of v "-1 :: complex mpoly"] by simp
    have "MPoly_Type.degree (signof p :: complex mpoly) v = 0"
      by (simp add: sign_def minus)
    then show ?thesis
      using prod mpoly_degree_mult_le[of "signof p" "(\<Prod>j<n. A $$ (j,p j))" v]
      by linarith
  qed
  have "MPoly_Type.degree
      (\<Sum>p\<in>?P. signof p * (\<Prod>j<n. A $$ (j,p j))) v
      \<le> (\<Sum>j<n. D j)"
    by (rule mpoly_degree_sum_le[OF finite]) (use bound in auto)
  then show ?thesis by (simp add: det_def'[OF mat] atLeast0LessThan)
qed

lemma mpoly_degree_resultant_weighted_le:
  fixes p q :: "complex mpoly poly"
  assumes cp: "\<And>k. MPoly_Type.degree (coeff p k) v \<le> Dp"
    and cq: "\<And>k. MPoly_Type.degree (coeff q k) v \<le> Dq"
  shows "MPoly_Type.degree (resultant p q) v \<le>
    degree q * Dp + degree p * Dq"
proof -
  let ?m = "degree p"
  let ?n = "degree q"
  let ?A = "sylvester_mat p q"
  have mat: "?A \<in> carrier_mat (?m+?n) (?m+?n)"
    by (rule sylvester_carrier_mat)
  have entries: "MPoly_Type.degree (?A $$ (j,k)) v \<le>
      (if j < ?n then Dp else Dq)"
    if "j < ?m+?n" "k < ?m+?n" for j k
    using cp cq that
    by (auto simp: sylvester_mat_def sylvester_mat_sub_def)
  have split: "(\<Sum>j<?m+?n. if j < ?n then Dp else Dq) =
      ?n * Dp + ?m * Dq"
  proof -
    have set: "{..< ?m+?n} = {..< ?n} \<union> {?n..< ?m+?n}"
      by auto
    show ?thesis
      unfolding set
      by (subst sum.union_disjoint) auto
  qed
  have "MPoly_Type.degree (det ?A) v \<le>
      (\<Sum>j<?m+?n. if j < ?n then Dp else Dq)"
    by (rule mpoly_degree_det_row_le[OF mat entries])
  then show ?thesis
    by (simp add: resultant_def split)
qed

lemma mpoly_degree_det_le:
  fixes A :: "complex mpoly mat"
  assumes mat: "A \<in> carrier_mat n n"
    and entries: "\<And>j k. j < n \<Longrightarrow> k < n \<Longrightarrow>
      MPoly_Type.degree (A $$ (j,k)) v \<le> D"
  shows "MPoly_Type.degree (det A) v \<le> n * D"
proof -
  have "MPoly_Type.degree (det A) v \<le> (\<Sum>j<n. (\<lambda>_. D) j)"
    by (rule mpoly_degree_det_row_le[OF mat]) (use entries in auto)
  then show ?thesis by simp
qed

lemma mpoly_degree_resultant_le:
  fixes p q :: "complex mpoly poly"
  assumes cp: "\<And>k. MPoly_Type.degree (coeff p k) v \<le> D"
    and cq: "\<And>k. MPoly_Type.degree (coeff q k) v \<le> D"
  shows "MPoly_Type.degree (resultant p q) v \<le> (degree p + degree q) * D"
proof -
  have "MPoly_Type.degree (resultant p q) v \<le> degree q * D + degree p * D"
    by (rule mpoly_degree_resultant_weighted_le[OF cp cq])
  then show ?thesis by (simp add: algebra_simps)
qed

lemma degree_coeff_first_deriv_le:
  fixes F :: "complex mpoly"
  shows "MPoly_Type.degree (coeff (pderiv (mpoly_to_mpoly_poly 0 F)) k) 1
    \<le> MPoly_Type.degree F 1"
proof -
  let ?p = "mpoly_to_mpoly_poly 0 F"
  have scalar: "MPoly_Type.degree (1 + of_nat k :: complex mpoly) 1 = 0"
    by (simp add: nat_scalar_mpoly degree_eq_0_iff vars_empty_iff)
  have "MPoly_Type.degree ((1 + of_nat k) * coeff ?p (Suc k)) 1 \<le>
    MPoly_Type.degree (1 + of_nat k :: complex mpoly) 1 +
      MPoly_Type.degree (coeff ?p (Suc k)) 1"
    using mpoly_degree_mult_le[of "1 + of_nat k" "coeff ?p (Suc k)" 1] by simp
  also have "... \<le> MPoly_Type.degree F 1"
    using scalar degree_coeff_first_le[of F "Suc k"] by simp
  finally show ?thesis by (simp add: coeff_pderiv)
qed

lemma first_resultant_degree_le:
  "MPoly_Type.degree (first_resultant F) 1 \<le>
    2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
proof -
  let ?p = "mpoly_to_mpoly_poly 0 F"
  let ?D = "MPoly_Type.degree F 1"
  have "MPoly_Type.degree (first_resultant F) 1 \<le>
    (degree ?p + degree (pderiv ?p)) * ?D"
  proof -
    have cp: "MPoly_Type.degree (coeff ?p k) 1 \<le> ?D" for k
      by (rule degree_coeff_first_le)
    have cq: "MPoly_Type.degree (coeff (pderiv ?p) k) 1 \<le> ?D" for k
      by (rule degree_coeff_first_deriv_le)
    show ?thesis unfolding first_resultant_def
      by (rule mpoly_degree_resultant_le[OF cp cq])
  qed
  also have "... \<le> (2 * degree ?p) * ?D"
    by (intro mult_le_mono1) (simp add: degree_pderiv)
  finally show ?thesis by simp
qed

lemma first_resultant_poly_degree_le:
  "degree (first_resultant_poly F) \<le>
    2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
  using first_resultant_degree_le[of F] degree_mpoly_to_poly_le[of 1 "first_resultant F"]
  by (simp add: first_resultant_poly_def)

lemma determinant_zero_rows_order_set:
  fixes A :: "complex poly mat"
  assumes mat: "A \<in> carrier_mat n n"
    and rows: "I \<subseteq> {..<n}"
    and zeros: "\<And>i j. i \<in> I \<Longrightarrow> j < n \<Longrightarrow> poly (A $$ (i,j)) a = 0"
    and nz: "det A \<noteq> 0"
  shows "card I \<le> Polynomial.order a (det A)"
proof -
  let ?L = "[:-a,1:]"
  let ?P = "{p. p permutes {..<n}}"
  have fin: "finite I" using rows finite_subset by blast
  have each: "?L ^ card I dvd signof p * (\<Prod>i<n. A $$ (i,p i))"
    if "p \<in> ?P" for p
  proof -
    have pi: "p i < n" if "i \<in> I" for i
    proof -
      have "i < n" using that rows by auto
      then show ?thesis using \<open>p \<in> ?P\<close>
        by (metis lessThan_iff mem_Collect_eq permutes_in_image)
    qed
    have d: "?L dvd A $$ (i,p i)" if "i \<in> I" for i
      using zeros[OF that pi[OF that]] by (simp add: poly_eq_0_iff_dvd)
    have "(\<Prod>i\<in>I. ?L) dvd (\<Prod>i\<in>I. A $$ (i,p i))"
      by (rule prod_dvd_prod) (use d in auto)
    then have "?L ^ card I dvd (\<Prod>i\<in>I. A $$ (i,p i))"
      using fin by simp
    also have "(\<Prod>i\<in>I. A $$ (i,p i)) dvd (\<Prod>i<n. A $$ (i,p i))"
      by (rule prod_dvd_prod_subset) (use rows in auto)
    finally show ?thesis by (metis dvd_mult2 mult.commute)
  qed
  have "?L ^ card I dvd det A"
    unfolding det_def'[OF mat] atLeast0LessThan
    by (rule dvd_sum) (use each in auto)
  then show ?thesis using nz order_divides[of a "card I" "det A"] by blast
qed

lemma determinant_zero_columns_order_set:
  fixes A :: "complex poly mat"
  assumes mat: "A \<in> carrier_mat n n"
    and cols: "J \<subseteq> {..<n}"
    and zeros: "\<And>i j. j \<in> J \<Longrightarrow> i < n \<Longrightarrow> poly (A $$ (i,j)) a = 0"
    and nz: "det A \<noteq> 0"
  shows "card J \<le> Polynomial.order a (det A)"
proof -
  have tr: "transpose_mat A \<in> carrier_mat n n" using mat by simp
  have dz: "\<And>i j. i \<in> J \<Longrightarrow> j < n \<Longrightarrow>
      poly (transpose_mat A $$ (i,j)) a = 0"
  proof -
    fix i j
    assume ij: "i \<in> J" "j < n"
    have "i < n" using cols ij(1) by auto
    then have "transpose_mat A $$ (i,j) = A $$ (j,i)"
      using mat ij(2) by simp
    then show "poly (transpose_mat A $$ (i,j)) a = 0"
      using zeros[OF ij(1) ij(2)] by simp
  qed
  have nztr: "det (transpose_mat A) \<noteq> 0"
    using nz det_transpose[OF mat] by simp
  have "card J \<le> Polynomial.order a (det (transpose_mat A))"
    by (rule determinant_zero_rows_order_set[OF tr cols dz nztr])
  then show ?thesis using det_transpose[OF mat] by simp
qed

lemma pcompose_power_complex:
  fixes p q :: "complex poly"
  shows "pcompose (p ^ n) q = pcompose p q ^ n"
  by (induction n) (simp_all add: pcompose_mult)

lemma coeff_translate_below_order:
  fixes f :: "complex poly"
  assumes lt: "k < Polynomial.order x f"
  shows "coeff (pcompose f [:x, 1:]) k = 0"
proof -
  let ?L = "[:-x, 1:]"
  let ?T = "[:x, 1:]"
  let ?m = "Polynomial.order x f"
  have p: "pcompose ?L ?T = [:0, 1:]"
    by (rule poly_ext) (simp add: poly_pcompose)
  have pow: "pcompose (?L ^ n) ?T = [:0, 1:] ^ n" for n
    using p by (simp add: pcompose_power_complex)
  have dvd: "?L ^ ?m dvd f" by (rule order_1)
  then obtain h where eq: "f = ?L ^ ?m * h"
    unfolding dvd_def by blast
  have step: "pcompose f ?T = pcompose (?L ^ ?m * h) ?T"
    by (rule arg_cong[OF eq])
  have shifted: "pcompose f ?T = [:0, 1:] ^ ?m * pcompose h ?T"
    using step by (simp only: pcompose_mult pow)
  have mon: "monom 1 ?m = [:0, 1:] ^ ?m"
    by (simp add: monom_altdef)
  have fact: "pcompose f ?T = monom 1 ?m * pcompose h ?T"
    unfolding mon by (rule shifted)
  have "monom 1 ?m dvd pcompose f ?T"
    using fact unfolding dvd_def by blast
  then show ?thesis using monom_1_dvd_iff' lt by blast
qed

definition taylor_column_change :: "nat \<Rightarrow> complex \<Rightarrow> complex mat" where
  "taylor_column_change N x =
    mat N N (\<lambda>(i,j). coeff ([:x, 1:] ^ (N - 1 - i)) (N - 1 - j))"

lemma taylor_column_change_carrier [simp]:
  "taylor_column_change N x \<in> carrier_mat N N"
  by (simp add: taylor_column_change_def)

lemma taylor_column_change_upper:
  "upper_triangular (taylor_column_change N x)"
proof (rule upper_triangularI)
  fix i j
  assume ji: "j < i" and iN: "i < dim_row (taylor_column_change N x)"
  have i: "i < N" using iN by (simp add: taylor_column_change_def)
  have j: "j < N" using ji i by arith
  have big: "N - 1 - i < N - 1 - j" using i j ji by arith
  have deg: "degree ([:x, 1:] ^ (N - 1 - i)) = N - 1 - i"
    by (rule degree_linear_power)
  have idx: "taylor_column_change N x $$ (i,j) =
      coeff ([:x, 1:] ^ (N - 1 - i)) (N - 1 - j)"
    using i j by (simp add: taylor_column_change_def)
  have "degree ([:x, 1:] ^ (N - 1 - i)) < N - 1 - j"
    using deg big by simp
  then have "coeff ([:x, 1:] ^ (N - 1 - i)) (N - 1 - j) = 0"
    by (rule coeff_eq_0)
  with idx show "taylor_column_change N x $$ (i,j) = 0" by simp
qed

lemma taylor_column_change_diag:
  "diag_mat (taylor_column_change N x) = replicate N 1"
proof (rule nth_equalityI)
  show "length (diag_mat (taylor_column_change N x)) = length (replicate N 1)"
    by (simp add: diag_mat_def taylor_column_change_def)
  fix i
  assume i: "i < length (diag_mat (taylor_column_change N x))"
  then have iN: "i < N" by (simp add: diag_mat_def taylor_column_change_def)
  have "diag_mat (taylor_column_change N x) ! i =
      coeff ([:x, 1:] ^ (N - 1 - i)) (N - 1 - i)"
    using iN by (simp add: diag_mat_def taylor_column_change_def)
  also have "... = 1" by (rule coeff_linear_power)
  finally show "diag_mat (taylor_column_change N x) ! i = replicate N 1 ! i"
    using iN by simp
qed

lemma taylor_column_change_det [simp]:
  "det (taylor_column_change N x) = 1"
  using det_upper_triangular
    [OF taylor_column_change_upper taylor_column_change_carrier]
  by (simp add: taylor_column_change_diag)

definition descending_row_polynomial :: "nat \<Rightarrow> 'a::comm_semiring_1 mat \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "descending_row_polynomial N A i =
    (\<Sum>j<N. monom (A $$ (i,j)) (N - 1 - j))"

lemma coeff_descending_row_polynomial:
  fixes A :: "'a::comm_semiring_1 mat"
  assumes k: "k < N"
  shows "coeff (descending_row_polynomial N A i) k = A $$ (i, N - 1 - k)"
proof -
  have eq: "(N - 1 - j = k) \<longleftrightarrow> (j = N - 1 - k)" if "j < N" for j
    using that k by arith
  have "coeff (descending_row_polynomial N A i) k =
      (\<Sum>j<N. if N - 1 - j = k then A $$ (i,j) else 0)"
    by (simp add: descending_row_polynomial_def Polynomial.coeff_sum)
  also have "... = (\<Sum>j<N. if j = N - 1 - k then A $$ (i,j) else 0)"
  proof (rule sum.cong)
    show "{..<N} = {..<N}" by simp
    fix j
    assume "j \<in> {..<N}"
    then have "j < N" by simp
    then show "(if N - 1 - j = k then A $$ (i,j) else 0) =
      (if j = N - 1 - k then A $$ (i,j) else 0)"
      using eq[of j] by simp
  qed
  also have "... = A $$ (i, N - 1 - k)"
  proof -
    have fin: "finite {..<N}" by simp
    have "N - 1 - k < N" using k by arith
    then have mem: "N - 1 - k \<in> {..<N}" by simp
    show ?thesis using mem
      by (simp only: sum.delta[OF fin]) simp
  qed
  finally show ?thesis .
qed

lemma coeff_descending_row_polynomial_high:
  fixes A :: "'a::comm_semiring_1 mat"
  assumes k: "N \<le> k"
  shows "coeff (descending_row_polynomial N A i) k = 0"
proof -
  have "coeff (descending_row_polynomial N A i) k =
      (\<Sum>j<N. if N - 1 - j = k then A $$ (i,j) else 0)"
    by (simp add: descending_row_polynomial_def Polynomial.coeff_sum)
  also have "... = 0"
  proof (rule sum.neutral, intro ballI)
    fix j
    assume "j \<in> {..<N}"
    then have jN: "j < N" by simp
    have "N - 1 - j < k" using k jN by arith
    then show "(if N - 1 - j = k then A $$ (i,j) else 0) = 0" by simp
  qed
  finally show ?thesis .
qed

lemma sylvester_descending_row_polynomial:
  fixes p q :: "complex poly poly"
  defines "N \<equiv> degree p + degree q"
  assumes i: "i < N"
  shows "descending_row_polynomial N (sylvester_mat p q) i =
    (if i < degree q then monom 1 (degree q - 1 - i) * p
     else monom 1 (N - 1 - i) * q)"
proof (rule poly_eqI)
  fix k
  let ?A = "sylvester_mat p q"
  show "coeff (descending_row_polynomial N ?A i) k =
    coeff (if i < degree q then monom 1 (degree q - 1 - i) * p
      else monom 1 (N - 1 - i) * q) k"
  proof (cases "k < N")
    case True
    let ?j = "N - 1 - k"
    have j: "?j < N" using True by arith
    have sj: "N - ?j = Suc k" using True by arith
    have sj2: "N - (N - Suc k) = Suc k" using True by arith
    have idx: "?A $$ (i,?j) =
      (if i < degree q then coeff (monom 1 (degree q - i) * p) (N - ?j)
       else coeff (monom 1 (N - i) * q) (N - ?j))"
      using sylvester_index_mat2[where p=p and q=q and i=i and j="N - 1 - k"] i j
      by (simp add: N_def)
    have "coeff (descending_row_polynomial N ?A i) k = ?A $$ (i,?j)"
      by (rule coeff_descending_row_polynomial[OF True])
    also have "... = coeff (if i < degree q then monom 1 (degree q - 1 - i) * p
      else monom 1 (N - 1 - i) * q) k"
    proof (cases "i < degree q")
      case True
      have exp: "degree q - i = Suc (degree q - 1 - i)"
        using True by arith
      show ?thesis using idx True
        by (simp add: sj sj2 exp coeff_monom_Suc)
    next
      case False
      have exp: "N - i = Suc (N - 1 - i)" using i by arith
      show ?thesis using idx False
        by (simp add: sj sj2 exp coeff_monom_Suc)
    qed
    finally show ?thesis .
  next
    case False
    have kn: "N \<le> k" using False by simp
    have lhs: "coeff (descending_row_polynomial N ?A i) k = 0"
      by (rule coeff_descending_row_polynomial_high[OF kn])
    have rhs: "coeff (if i < degree q then monom 1 (degree q - 1 - i) * p
      else monom 1 (N - 1 - i) * q) k = 0"
      using kn i by (auto simp: N_def coeff_monom_mult coeff_eq_0)
    show ?thesis using lhs rhs by simp
  qed
qed

lemma descending_row_polynomial_map:
  fixes A :: "'a::comm_semiring_1 mat"
    and h :: "'a \<Rightarrow> 'b::comm_semiring_1"
  assumes mat: "A \<in> carrier_mat N N" and i: "i < N" and h0: "h 0 = 0"
  shows "descending_row_polynomial N (map_mat h A) i =
    map_poly h (descending_row_polynomial N A i)"
proof (rule poly_eqI)
  fix k
  show "coeff (descending_row_polynomial N (map_mat h A) i) k =
    coeff (map_poly h (descending_row_polynomial N A i)) k"
  proof (cases "k < N")
    case True
    have j: "N - 1 - k < N" using True by arith
    have "coeff (descending_row_polynomial N (map_mat h A) i) k =
        map_mat h A $$ (i, N - 1 - k)"
      by (rule coeff_descending_row_polynomial[OF True])
    also have "... = h (A $$ (i, N - 1 - k))"
      using mat i j by simp
    also have "... = coeff (map_poly h (descending_row_polynomial N A i)) k"
      using True h0 by (simp add: coeff_map_poly coeff_descending_row_polynomial)
    finally show ?thesis .
  next
    case False
    then have kn: "N \<le> k" by simp
    then show ?thesis using h0
      by (simp add: coeff_descending_row_polynomial_high coeff_map_poly)
  qed
qed

lemma determinant_zero_columns_order_after_constant_change:
  fixes A :: "complex poly mat" and B :: "complex mat"
  assumes mat: "A \<in> carrier_mat N N" and bm: "B \<in> carrier_mat N N"
    and detB: "det B = 1" and cols: "J \<subseteq> {..<N}"
    and zeros: "\<And>i j. i < N \<Longrightarrow> j \<in> J \<Longrightarrow>
      (map_mat (\<lambda>p::complex poly. poly p a) A * B) $$ (i,j) = 0"
    and nz: "det A \<noteq> 0"
  shows "card J \<le> Polynomial.order a (det A)"
proof -
  let ?C = "map_mat (\<lambda>z::complex. [:z:]) B"
  interpret c: comm_ring_hom "\<lambda>z::complex. [:z:]"
    by (unfold_locales; simp)
  have cm: "?C \<in> carrier_mat N N" using bm by simp
  have dc: "det ?C = 1" using detB by simp
  have ec: "map_mat (\<lambda>p::complex poly. poly p a) ?C = B"
    by (rule eq_matI) (use bm in auto)
  have em: "map_mat (\<lambda>p::complex poly. poly p a) (A * ?C) =
      map_mat (\<lambda>p::complex poly. poly p a) A * B"
  proof (rule eq_matI)
    show "dim_row (map_mat (\<lambda>p::complex poly. poly p a) (A * ?C)) =
      dim_row (map_mat (\<lambda>p::complex poly. poly p a) A * B)"
      using mat cm bm by simp
    show "dim_col (map_mat (\<lambda>p::complex poly. poly p a) (A * ?C)) =
      dim_col (map_mat (\<lambda>p::complex poly. poly p a) A * B)"
      using mat cm bm by simp
    fix i j
    assume ij: "i < dim_row (map_mat (\<lambda>p::complex poly. poly p a) A * B)"
      "j < dim_col (map_mat (\<lambda>p::complex poly. poly p a) A * B)"
    then have i: "i < N" and j: "j < N" using mat bm by simp_all
    show "map_mat (\<lambda>p::complex poly. poly p a) (A * ?C) $$ (i,j) =
      (map_mat (\<lambda>p::complex poly. poly p a) A * B) $$ (i,j)"
      using mat cm bm i j ec
      by (simp add: scalar_prod_def atLeast0LessThan poly_sum mult.commute)
  qed
  have dm: "det (A * ?C) = det A"
    using det_mult[OF mat cm] dc by simp
  have z: "poly ((A * ?C) $$ (i,j)) a = 0" if "i < N" "j \<in> J" for i j
  proof -
    have j: "j < N" using cols that(2) by auto
    have "poly ((A * ?C) $$ (i,j)) a = map_mat (\<lambda>p::complex poly. poly p a) (A * ?C) $$ (i,j)"
      using mat cm that(1) j by simp
    also have "... = 0" using zeros[OF that] em by simp
    finally show ?thesis .
  qed
  have "card J \<le> Polynomial.order a (det (A * ?C))"
    by (rule determinant_zero_columns_order_set[OF mult_carrier_mat[OF mat cm]
      cols z]) (use nz dm in auto)
  then show ?thesis using dm by simp
qed

lemma map_poly_monom_one_mult:
  fixes h :: "'a::comm_semiring_1 \<Rightarrow> 'b::comm_semiring_1"
  assumes h0: "h 0 = 0"
  shows "map_poly h (monom 1 t * f) = monom 1 t * map_poly h f"
  by (rule poly_eqI) (simp add: coeff_map_poly h0 coeff_monom_mult)

lemma coeff_pcompose_shift_zero:
  fixes f :: "complex poly"
  assumes k: "k < Polynomial.order x f"
  shows "coeff (pcompose (monom 1 t * f) [:x,1:]) k = 0"
proof -
  have d: "monom 1 (Polynomial.order x f) dvd pcompose f [:x,1:]"
    unfolding monom_1_dvd_iff'
    using coeff_translate_below_order by blast
  have d2: "monom 1 (Polynomial.order x f) dvd
      pcompose (monom 1 t * f) [:x,1:]"
    using d by (metis dvd_mult2 mult.commute pcompose_mult)
  show ?thesis using d2 k by (simp add: monom_1_dvd_iff')
qed

lemma specialized_sylvester_descending_row:
  fixes p q :: "complex poly poly"
  defines "N \<equiv> degree p + degree q"
  assumes i: "i < N"
  shows "descending_row_polynomial N
      (map_mat (\<lambda>r::complex poly. poly r a) (sylvester_mat p q)) i =
    (if i < degree q then
      monom 1 (degree q - 1 - i) * map_poly (\<lambda>r. poly r a) p
     else monom 1 (N - 1 - i) * map_poly (\<lambda>r. poly r a) q)"
proof -
  have mat: "sylvester_mat p q \<in> carrier_mat N N"
    unfolding N_def by (rule sylvester_carrier_mat)
  have row: "descending_row_polynomial N (sylvester_mat p q) i =
      (if i < degree q then monom 1 (degree q - 1 - i) * p
       else monom 1 (N - 1 - i) * q)"
    unfolding N_def
    by (rule sylvester_descending_row_polynomial) (use i in \<open>simp add: N_def\<close>)
  have "descending_row_polynomial N
      (map_mat (\<lambda>r::complex poly. poly r a) (sylvester_mat p q)) i =
      map_poly (\<lambda>r. poly r a) (descending_row_polynomial N (sylvester_mat p q) i)"
    by (rule descending_row_polynomial_map[OF mat i]) simp
  then show ?thesis
    by (simp add: row map_poly_monom_one_mult)
qed

lemma pcompose_monom_complex:
  fixes q :: "complex poly"
  shows "pcompose (monom c n) q = Polynomial.smult c (q ^ n)"
  by (simp add: monom_altdef pcompose_smult pcompose_power_complex
      pcompose_pCons)

lemma taylor_product_entry:
  fixes A :: "complex mat"
  assumes mat: "A \<in> carrier_mat N N" and i: "i < N" and j: "j < N"
  shows "(A * taylor_column_change N x) $$ (i,j) =
    coeff (pcompose (descending_row_polynomial N A i) [:x, 1:]) (N - 1 - j)"
proof -
  have lhs: "(A * taylor_column_change N x) $$ (i,j) =
      (\<Sum>k<N. A $$ (i,k) * coeff ([:x, 1:] ^ (N - 1 - k)) (N - 1 - j))"
    using mat i j
    by (simp add: scalar_prod_def taylor_column_change_def atLeast0LessThan)
  have rhs: "coeff (pcompose (descending_row_polynomial N A i) [:x, 1:]) (N - 1 - j) =
      (\<Sum>k<N. A $$ (i,k) * coeff ([:x, 1:] ^ (N - 1 - k)) (N - 1 - j))"
    by (simp add: descending_row_polynomial_def pcompose_sum
      pcompose_monom_complex Polynomial.coeff_sum)
  show ?thesis using lhs rhs by simp
qed

text \<open>Green, Appendix A, Lemma A.1: the full root-multiplicity estimate.
  The Taylor column change moves an arbitrary root to the coefficient origin
  without changing the Sylvester determinant.\<close>

lemma first_resultant_multiplicity_irreducible:
  assumes bv: "bivariate F" and irr: "irreducible F"
    and pos: "0 < MPoly_Type.degree F 0"
  shows "Polynomial.order x (specialize_second a F) \<le>
    1 + Polynomial.order a (first_resultant_poly F)"
proof -
  let ?f = "specialize_second a F"
  let ?mu = "Polynomial.order x ?f"
  let ?d = "MPoly_Type.degree F 0"
  let ?n = "?d - 1"
  let ?N = "?d + ?n"
  let ?m = "?mu - 1"
  let ?P = "bivariate_as_poly_poly F"
  let ?A = "sylvester_mat ?P (pderiv ?P)"
  have fnz: "?f \<noteq> 0"
    by (rule irreducible_specialize_second_nonzero[OF bv irr pos])
  have rnz: "first_resultant_poly F \<noteq> 0"
    by (rule first_resultant_nonzero_irreducible[OF bv irr pos])
  show ?thesis
  proof (cases "?mu \<le> 1")
    case True
    then show ?thesis by simp
  next
    case False
    then have mu: "2 \<le> ?mu" by simp
    have mpos: "0 < ?m" using mu by simp
    have deg: "degree ?f \<le> ?d"
      using degree_specialize_first[of "\<lambda>_. a" 0 F] by simp
    have ord: "?mu \<le> degree ?f" using order_degree[OF fnz, of x] .
    have mn: "?m \<le> ?n" using ord deg mu pos by arith
    let ?J = "{?N - ?m ..< ?N}"
    have jcard: "card ?J = ?m" using mn by simp
    have jsub: "?J \<subseteq> {..< ?N}" by auto
    have sp: "map_poly (\<lambda>q::complex poly. poly q a) ?P = ?f"
      by (rule specialize_bivariate_as_poly_poly[OF bv])
    have cp: "poly (coeff ?P k) a = coeff ?f k" for k
    proof -
      have "coeff (map_poly (\<lambda>q::complex poly. poly q a) ?P) k =
          poly (coeff ?P k) a"
        by (subst coeff_map_poly) simp_all
      with sp show ?thesis by simp
    qed
    have spd: "map_poly (\<lambda>q::complex poly. poly q a) (pderiv ?P) =
        pderiv ?f"
    proof (rule poly_eqI)
      fix k
      have "coeff (map_poly (\<lambda>q::complex poly. poly q a) (pderiv ?P)) k =
          poly (coeff (pderiv ?P) k) a"
        by (subst coeff_map_poly) simp_all
      also have "... = coeff (pderiv ?f) k"
        by (simp add: coeff_pderiv cp)
      finally show "coeff (map_poly (\<lambda>q::complex poly. poly q a)
          (pderiv ?P)) k = coeff (pderiv ?f) k" .
    qed
    have pd: "degree ?P = ?d" by (rule degree_bivariate_as_poly_poly[OF bv])
    have dd: "degree (pderiv ?P) = ?n"
      using pd pos by (simp add: degree_pderiv)
    have N_eq: "?N = degree ?P + degree (pderiv ?P)"
      using pd dd by simp
    have mat: "?A \<in> carrier_mat ?N ?N"
      unfolding N_eq by (rule sylvester_carrier_mat)
    have det: "det ?A = first_resultant_poly F"
      by (simp add: first_resultant_poly_nested[OF bv] resultant_def)
    have nzA: "det ?A \<noteq> 0" using det rnz by simp
    have row: "descending_row_polynomial ?N
        (map_mat (\<lambda>q::complex poly. poly q a) ?A) i =
        (if i < ?n then monom 1 (?n - 1 - i) * ?f
         else monom 1 (?N - 1 - i) * pderiv ?f)" if i: "i < ?N" for i
    proof -
      have ibound: "i < degree ?P + degree (pderiv ?P)"
        using i N_eq by arith
      have raw: "descending_row_polynomial ?N
          (map_mat (\<lambda>q::complex poly. poly q a) ?A) i =
          (if i < degree (pderiv ?P) then
            monom 1 (degree (pderiv ?P) - 1 - i) *
              map_poly (\<lambda>q. poly q a) ?P
           else monom 1 (?N - 1 - i) *
              map_poly (\<lambda>q. poly q a) (pderiv ?P))"
        unfolding N_eq
        by (rule specialized_sylvester_descending_row)
          (use ibound in \<open>simp add: N_eq\<close>)
      show ?thesis using raw by (simp add: dd sp spd)
    qed
    have root: "poly ?f x = 0" using fnz mu by (simp add: order_root)
    have dor: "?mu = Suc (Polynomial.order x (pderiv ?f))"
      by (rule order_pderiv[OF fnz root])
    have dm: "Polynomial.order x (pderiv ?f) = ?m"
      using dor mu by arith
    have zero: "(map_mat (\<lambda>q::complex poly. poly q a) ?A *
        taylor_column_change ?N x) $$ (i,j) = 0"
      if i: "i < ?N" and j: "j \<in> ?J" for i j
    proof -
      have jl: "?N - ?m \<le> j" and jN: "j < ?N" using j by auto
      have k: "?N - 1 - j < ?m" using jl jN mn mpos by arith
      have kf: "?N - 1 - j < Polynomial.order x ?f"
        using k mu by arith
      have kd: "?N - 1 - j < Polynomial.order x (pderiv ?f)"
        using k dm by simp
      have zf: "coeff (pcompose (monom 1 (?n - 1 - i) * ?f) [:x,1:])
          (?N - 1 - j) = 0"
        by (rule coeff_pcompose_shift_zero[OF kf])
      have zd: "coeff (pcompose (monom 1 (?N - 1 - i) * pderiv ?f)
          [:x,1:]) (?N - 1 - j) = 0"
        by (rule coeff_pcompose_shift_zero[OF kd])
      have entry: "(map_mat (\<lambda>q::complex poly. poly q a) ?A *
          taylor_column_change ?N x) $$ (i,j) =
          coeff (pcompose (descending_row_polynomial ?N
            (map_mat (\<lambda>q::complex poly. poly q a) ?A) i)
            [:x,1:]) (?N - 1 - j)"
        by (rule taylor_product_entry) (use mat i jN in auto)
      have rhs: "coeff (pcompose (descending_row_polynomial ?N
          (map_mat (\<lambda>q::complex poly. poly q a) ?A) i)
          [:x,1:]) (?N - 1 - j) = 0"
      proof (cases "i < ?n")
        case True
        have rr: "descending_row_polynomial ?N
            (map_mat (\<lambda>q::complex poly. poly q a) ?A) i =
            monom 1 (?n - 1 - i) * ?f"
          using row[OF i] True by simp
        show ?thesis unfolding rr by (rule zf)
      next
        case False
        have rr: "descending_row_polynomial ?N
            (map_mat (\<lambda>q::complex poly. poly q a) ?A) i =
            monom 1 (?N - 1 - i) * pderiv ?f"
          using row[OF i] False by simp
        show ?thesis unfolding rr by (rule zd)
      qed
      show ?thesis using entry rhs by simp
    qed
    have ordm: "?m \<le> Polynomial.order a (first_resultant_poly F)"
      using determinant_zero_columns_order_after_constant_change
        [OF mat taylor_column_change_carrier taylor_column_change_det
          jsub zero nzA] jcard det by simp
    have "?mu = ?m + 1" using mu by arith
    with ordm show ?thesis by arith
  qed
qed

lemma determinant_zero_rows_order:
  fixes A :: "complex poly mat"
  assumes mat: "A \<in> carrier_mat n n"
    and mn: "m \<le> n"
    and zeros: "\<And>i j. i < m \<Longrightarrow> j < n \<Longrightarrow> poly (A $$ (i,j)) a = 0"
    and nz: "det A \<noteq> 0"
  shows "m \<le> Polynomial.order a (det A)"
proof -
  have rows: "{..<m} \<subseteq> {..<n}" using mn by auto
  have z: "\<And>i j. i \<in> {..<m} \<Longrightarrow> j < n \<Longrightarrow> poly (A $$ (i,j)) a = 0"
    using zeros by simp
  show ?thesis using determinant_zero_rows_order_set[OF mat rows z nz] by simp
qed

lemma first_resultant_bad_parameters_card:
  assumes "first_resultant_poly F \<noteq> 0"
  shows "card {a. poly (first_resultant_poly F) a = 0} \<le>
    2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
  using poly_roots_degree[OF assms] first_resultant_poly_degree_le[of F]
  by linarith

definition exceptional_first_fibre :: "complex mpoly \<Rightarrow> complex \<Rightarrow> bool" where
  "exceptional_first_fibre F a \<longleftrightarrow>
    degree (specialize_second a F) < MPoly_Type.degree F 0 \<or>
    (\<exists>x. 2 \<le> Polynomial.order x (specialize_second a F))"

lemma first_resultant_exceptional_fibre_zero:
  assumes bv: "bivariate F" and irr: "irreducible F"
    and pos: "0 < MPoly_Type.degree F 0"
    and ex: "exceptional_first_fibre F a"
  shows "poly (first_resultant_poly F) a = 0"
proof -
  have nz: "specialize_second a F \<noteq> 0"
    by (rule irreducible_specialize_second_nonzero[OF bv irr pos])
  from ex have "degree (specialize_second a F) < MPoly_Type.degree F 0 \<or>
      (\<exists>x. 2 \<le> Polynomial.order x (specialize_second a F))"
    by (simp add: exceptional_first_fibre_def)
  then show ?thesis
  proof
    assume drop: "degree (specialize_second a F) < MPoly_Type.degree F 0"
    show ?thesis by (rule first_resultant_degree_drop[OF bv pos drop])
  next
    assume "\<exists>x. 2 \<le> Polynomial.order x (specialize_second a F)"
    then obtain x where mult: "2 \<le> Polynomial.order x (specialize_second a F)"
      by blast
    show ?thesis by (rule first_resultant_double_root_any[OF bv pos nz mult])
  qed
qed

lemma first_resultant_exceptional_fibre_card:
  assumes bv: "bivariate F" and irr: "irreducible F"
    and pos: "0 < MPoly_Type.degree F 0"
  shows "card {a. exceptional_first_fibre F a} \<le>
    2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
proof -
  have rnz: "first_resultant_poly F \<noteq> 0"
    by (rule first_resultant_nonzero_irreducible[OF bv irr pos])
  have sub: "{a. exceptional_first_fibre F a} \<subseteq>
      {a. poly (first_resultant_poly F) a = 0}"
    using first_resultant_exceptional_fibre_zero[OF bv irr pos] by auto
  have "card {a. exceptional_first_fibre F a} \<le>
      card {a. poly (first_resultant_poly F) a = 0}"
    by (rule card_mono[OF poly_roots_finite[OF rnz] sub])
  also have "... \<le> 2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
    by (rule first_resultant_bad_parameters_card[OF rnz])
  finally show ?thesis .
qed

end
