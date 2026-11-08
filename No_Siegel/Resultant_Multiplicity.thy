theory Resultant_Multiplicity
  imports Bivariate_Polynomial Factor_Algebraic_Polynomial.Multivariate_Resultant
begin

declare [[apply_timeout=10]]

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
  have "poly (first_resultant_poly F) a =
      ?h (det (sylvester_mat_sub (degree ?p) (degree (pderiv ?p)) ?p (pderiv ?p)))"
    using poly_first_resultant_poly[OF assms, of a]
    by (simp add: first_resultant_def resultant_def sylvester_mat_def)
  also have "... = det (h.mat_hom (sylvester_mat_sub
      (degree ?p) (degree (pderiv ?p)) ?p (pderiv ?p)))"
    unfolding h.hom_det ..
  also have "h.mat_hom (sylvester_mat_sub
      (degree ?p) (degree (pderiv ?p)) ?p (pderiv ?p)) =
      sylvester_mat_sub (degree ?p) (degree (pderiv ?p))
        (specialize_second a F) (pderiv (specialize_second a F))"
  proof -
    have cp0: "coeff (map_poly ?h ?p) k = ?h (coeff ?p k)" for k
      by (rule coeff_map_poly) simp
    have cd0: "coeff (map_poly ?h (pderiv ?p)) k =
        ?h (coeff (pderiv ?p) k)" for k
      by (rule coeff_map_poly) simp
    have cp: "?h (coeff ?p k) = coeff (specialize_second a F) k" for k
      using cp0[of k] eq by simp
    have cd: "?h (coeff (pderiv ?p) k) =
        coeff (pderiv (specialize_second a F)) k" for k
      using cd0[of k] der by simp
    show ?thesis
      by (intro eq_matI) (auto simp: sylvester_mat_sub_def cp cd)
  qed
  finally show ?thesis by simp
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

lemma mpoly_degree_det_le:
  fixes A :: "complex mpoly mat"
  assumes mat: "A \<in> carrier_mat n n"
    and entries: "\<And>j k. j < n \<Longrightarrow> k < n \<Longrightarrow> MPoly_Type.degree (A $$ (j,k)) v \<le> D"
  shows "MPoly_Type.degree (det A) v \<le> n * D"
proof -
  let ?P = "{p. p permutes {0..<n}}"
  have finite: "finite ?P" using finite_permutations by blast
  have bound: "MPoly_Type.degree (signof p * (\<Prod>j<n. A $$ (j,p j))) v \<le> n * D"
    if "p \<in> ?P" for p
  proof -
    have pj: "p j < n" if "j < n" for j
      using that \<open>p \<in> ?P\<close> by (simp add: permutes_in_image)
    have prod: "MPoly_Type.degree (\<Prod>j<n. A $$ (j,p j)) v \<le> n * D"
    proof -
      have "MPoly_Type.degree (\<Prod>j<n. A $$ (j,p j)) v \<le>
        (\<Sum>j<n. MPoly_Type.degree (A $$ (j,p j)) v)"
        by (rule mpoly_degree_prod_le) simp
      also have "... \<le> (\<Sum>j<n. D)"
        by (rule sum_mono) (auto intro: entries pj)
      finally show ?thesis by simp
    qed
    have minus: "MPoly_Type.degree (-1 :: complex mpoly) v = 0"
      using degree_mpoly_to_mpoly_poly[of v "-1 :: complex mpoly"] by simp
    have "MPoly_Type.degree (signof p :: complex mpoly) v = 0"
      by (simp add: sign_def minus)
    then show ?thesis using prod mpoly_degree_mult_le[of "signof p" "(\<Prod>j<n. A $$ (j,p j))" v]
      by linarith
  qed
  have "MPoly_Type.degree (\<Sum>p\<in>?P. signof p * (\<Prod>j<n. A $$ (j,p j))) v \<le> n * D"
    by (rule mpoly_degree_sum_le[OF finite]) (use bound in auto)
  then show ?thesis by (simp add: det_def'[OF mat] atLeast0LessThan)
qed

lemma mpoly_degree_resultant_le:
  fixes p q :: "complex mpoly poly"
  assumes cp: "\<And>k. MPoly_Type.degree (coeff p k) v \<le> D"
    and cq: "\<And>k. MPoly_Type.degree (coeff q k) v \<le> D"
  shows "MPoly_Type.degree (resultant p q) v \<le> (degree p + degree q) * D"
proof -
  let ?N = "degree p + degree q"
  let ?A = "sylvester_mat p q"
  have mat: "?A \<in> carrier_mat ?N ?N" by (rule sylvester_carrier_mat)
  have entries: "MPoly_Type.degree (?A $$ (j,k)) v \<le> D"
    if "j < ?N" "k < ?N" for j k
    using cp cq that by (auto simp: sylvester_mat_def sylvester_mat_sub_def)
  have "MPoly_Type.degree (det ?A) v \<le> ?N * D"
    by (rule mpoly_degree_det_le[OF mat]) (use entries in auto)
  then show ?thesis by (simp add: resultant_def)
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
    and rnz: "first_resultant_poly F \<noteq> 0"
  shows "card {a. exceptional_first_fibre F a} \<le>
    2 * MPoly_Type.degree F 0 * MPoly_Type.degree F 1"
proof -
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
