theory Quadratic_Gram
  imports Paper_Parameters
begin

text \<open>The coefficient pairing below is Green's quadratic trace pairing
  (Sections 2 and 4). It is positive for either sign of the discriminant.\<close>

definition green_quadratic_integer :: "int \<Rightarrow> complex \<Rightarrow> bool" where
  "green_quadratic_integer d z \<longleftrightarrow>
    (\<exists>a b::int. z = of_int a + of_int b * cpx_sqrt d)"

definition green_quad_embed :: "int \<Rightarrow> int \<times> int \<Rightarrow> complex" where
  "green_quad_embed d p = of_int (fst p) + of_int (snd p) * cpx_sqrt d"

lemma green_quad_embed_inj:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
  shows "inj (green_quad_embed d)"
proof (rule injI)
  fix p q :: "int \<times> int"
  obtain a b where p: "p = (a,b)" by (cases p) auto
  obtain c e where q: "q = (c,e)" by (cases q) auto
  assume equal: "green_quad_embed d p = green_quad_embed d q"
  have eq: "of_int a + of_int b * cpx_sqrt d =
    of_int c + of_int e * cpx_sqrt d"
    using equal by (simp add: p q green_quad_embed_def)
  have be: "b = e"
  proof (rule ccontr)
    assume ne: "b \<noteq> e"
    have "cpx_sqrt d * (of_int b - of_int e) = of_int c - of_int a"
      using eq by (simp add: algebra_simps)
    then have "cpx_sqrt d = (of_int c - of_int a) / (of_int b - of_int e)"
      using ne by (simp add: field_simps)
    then have "cpx_sqrt d \<in> Rats" by simp
    with irrational show False by contradiction
  qed
  have "a = c" using eq be by simp
  then show "p = q" using p q be by simp
qed

definition green_quad_coeff :: "int \<Rightarrow> complex \<Rightarrow> int \<times> int" where
  "green_quad_coeff d z = (SOME p. green_quad_embed d p = z)"

lemma green_quad_coeff_embed:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
  shows "green_quad_coeff d (green_quad_embed d p) = p"
proof (unfold green_quad_coeff_def, rule some_equality)
  show "green_quad_embed d p = green_quad_embed d p" by simp
  fix q :: "int \<times> int"
  assume eq: "green_quad_embed d q = green_quad_embed d p"
  show "q = p" by (rule injD[OF green_quad_embed_inj[OF irrational] eq])
qed

lemma green_quad_embed_coeff:
  assumes "green_quadratic_integer d z"
  shows "green_quad_embed d (green_quad_coeff d z) = z"
proof (unfold green_quad_coeff_def, rule someI_ex)
  show "\<exists>p. green_quad_embed d p = z"
    using assms by (auto simp: green_quadratic_integer_def
      green_quad_embed_def)
qed

definition green_quad_coeff_pair ::
  "int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int \<Rightarrow> int" where
  "green_quad_coeff_pair d p q =
    2 * (fst p * fst q + abs d * snd p * snd q)"

definition green_quad_trace_pair :: "int \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> int" where
  "green_quad_trace_pair d z w =
    green_quad_coeff_pair d (green_quad_coeff d z) (green_quad_coeff d w)"

lemma green_quad_trace_pair_embed:
  fixes p q :: "int \<times> int"
  assumes irrational: "cpx_sqrt d \<notin> Rats"
  shows "green_quad_trace_pair d (green_quad_embed d p)
    (green_quad_embed d q) =
    2 * (fst p * fst q + abs d * snd p * snd q)"
  by (simp add: green_quad_trace_pair_def green_quad_coeff_pair_def
    green_quad_coeff_embed[OF irrational])

lemma green_quad_trace_pair_sym:
  "green_quad_trace_pair d z w = green_quad_trace_pair d w z"
  by (simp add: green_quad_trace_pair_def green_quad_coeff_pair_def ac_simps)

definition green_quad_galois :: "int \<Rightarrow> complex \<Rightarrow> complex" where
  "green_quad_galois d z =
    green_quad_embed d
      (fst (green_quad_coeff d z), - snd (green_quad_coeff d z))"

definition green_quad_field_trace :: "int \<Rightarrow> complex \<Rightarrow> complex" where
  "green_quad_field_trace d z = z + green_quad_galois d z"

lemma green_quad_field_trace_embed:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
  shows "green_quad_field_trace d (green_quad_embed d (a,b)) = of_int (2*a)"
proof -
  have coeff: "green_quad_coeff d (green_quad_embed d (a,b)) = (a,b)"
    by (rule green_quad_coeff_embed[OF irrational])
  show ?thesis
    unfolding green_quad_field_trace_def green_quad_galois_def
    by (simp only: coeff fst_conv snd_conv;
      simp add: green_quad_embed_def algebra_simps)
qed

lemma green_quad_embed_mult:
  "green_quad_embed d (a,b) * green_quad_embed d (c,e) =
    green_quad_embed d (a * c + d * b * e, a * e + b * c)"
  using square_sqrt[of d]
  by (simp add: green_quad_embed_def algebra_simps power2_eq_square)

lemma cnj_cpx_sqrt:
  "cnj (cpx_sqrt d) = (if d < 0 then - cpx_sqrt d else cpx_sqrt d)"
  by (simp add: cpx_sqrt_def)

lemma green_quad_trace_pair_as_field_trace:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
  shows "of_int (green_quad_trace_pair d
      (green_quad_embed d (a,b)) (green_quad_embed d (c,e))) =
    green_quad_field_trace d
      (green_quad_embed d (a,b) * cnj (green_quad_embed d (c,e)))"
proof (cases "d < 0")
  case True
  have conjugate: "cnj (green_quad_embed d (c,e)) =
      green_quad_embed d (c,-e)"
    using True by (simp add: green_quad_embed_def cnj_cpx_sqrt algebra_simps)
  show ?thesis
    using True irrational
    by (simp add: conjugate green_quad_embed_mult
      green_quad_field_trace_embed green_quad_trace_pair_embed)
next
  case False
  have conjugate: "cnj (green_quad_embed d (c,e)) =
      green_quad_embed d (c,e)"
    using False by (simp add: green_quad_embed_def cnj_cpx_sqrt)
  show ?thesis
    using False irrational
    by (simp add: conjugate green_quad_embed_mult
      green_quad_field_trace_embed green_quad_trace_pair_embed)
qed

lemma green_quad_trace_pair_self_pos:
  assumes dnz: "d \<noteq> 0"
    and irrational: "cpx_sqrt d \<notin> Rats"
    and nz: "green_quad_embed d (a,b) \<noteq> 0"
  shows "0 < green_quad_trace_pair d
    (green_quad_embed d (a,b)) (green_quad_embed d (a,b))"
proof -
  have pair_nz: "a \<noteq> 0 \<or> b \<noteq> 0"
    using nz by (auto simp: green_quad_embed_def)
  have dpos: "0 < abs d" using dnz by simp
  have nonneg: "0 \<le> abs d * b^2" by simp
  have pos: "0 < a^2 + abs d * b^2"
  proof (cases "a = 0")
    case True
    then have "b \<noteq> 0" using pair_nz by simp
    then have "0 < b^2" by simp
    then show ?thesis using True dpos by simp
  next
    case False
    then have "0 < a^2" by simp
    with nonneg show ?thesis by linarith
  qed
  show ?thesis
    using pos by (simp add: green_quad_trace_pair_embed[OF irrational]
      power2_eq_square algebra_simps)

qed

lemma green_quadratic_integer_of_int [simp]:
  "green_quadratic_integer d (of_int a)"
  unfolding green_quadratic_integer_def
  by (rule exI[where x=a], rule exI[where x=0], simp)

lemma green_quadratic_integer_of_nat [simp]:
  "green_quadratic_integer d (of_nat n)"
  using green_quadratic_integer_of_int[of d "int n"] by simp

lemma green_quadratic_integer_sqrt [simp]:
  "green_quadratic_integer d (cpx_sqrt d)"
  unfolding green_quadratic_integer_def
  by (rule exI[where x=0], rule exI[where x=1], simp)

lemma green_quadratic_integer_add:
  assumes "green_quadratic_integer d z" "green_quadratic_integer d w"
  shows "green_quadratic_integer d (z + w)"
proof -
  obtain a b c e :: int where
    z: "z = of_int a + of_int b * cpx_sqrt d" and
    w: "w = of_int c + of_int e * cpx_sqrt d"
    using assms by (auto simp: green_quadratic_integer_def)
  show ?thesis
    unfolding green_quadratic_integer_def
    by (rule exI[where x="a + c"], rule exI[where x="b + e"],
      simp add: z w algebra_simps)
qed

lemma green_quadratic_integer_minus:
  assumes "green_quadratic_integer d z"
  shows "green_quadratic_integer d (- z)"
proof -
  obtain a b :: int where z: "z = of_int a + of_int b * cpx_sqrt d"
    using assms by (auto simp: green_quadratic_integer_def)
  show ?thesis
    unfolding green_quadratic_integer_def
    by (rule exI[where x="-a"], rule exI[where x="-b"],
      simp add: z algebra_simps)
qed

lemma green_quadratic_integer_mult:
  assumes "green_quadratic_integer d z" "green_quadratic_integer d w"
  shows "green_quadratic_integer d (z * w)"
proof -
  obtain a b c e :: int where
    z: "z = of_int a + of_int b * cpx_sqrt d" and
    w: "w = of_int c + of_int e * cpx_sqrt d"
    using assms by (auto simp: green_quadratic_integer_def)
  have eq: "z * w = of_int (a * c + d * b * e) +
    of_int (a * e + b * c) * cpx_sqrt d"
    unfolding z w using square_sqrt[of d]
    by (simp add: algebra_simps power2_eq_square)
  show ?thesis
    unfolding green_quadratic_integer_def
    by (rule exI[where x="a * c + d * b * e"],
      rule exI[where x="a * e + b * c"],
      simp add: eq)
qed

lemma green_quadratic_integer_power:
  assumes "green_quadratic_integer d z"
  shows "green_quadratic_integer d (z ^ n)"
  proof (induction n)
    case 0
    show ?case using green_quadratic_integer_of_int[of d 1] by simp
  next
    case (Suc n)
    show ?case by (simp add: green_quadratic_integer_mult[OF assms Suc.IH])
  qed

lemma green_monom_eval:
  "insertion alpha (MPoly_Type.monom (green_monom_index (r,s)) (1::complex)) =
    alpha 0 ^ r * alpha 1 ^ s"
proof -
  have eq: "MPoly_Type.monom (green_monom_index (r,s)) (1::complex) =
      MPoly_Type.monom (Poly_Mapping.single 0 r) 1 *
      MPoly_Type.monom (Poly_Mapping.single 1 s) 1"
    by (simp add: green_monom_index_def MPoly_Type.mult_monom)
  show ?thesis
    by (subst eq) (simp only: insertion_mult insertion_single mult_1)
qed

lemma green_specialized_monom:
  "specialize_second a (MPoly_Type.monom (green_monom_index (r,s)) (1::complex)) =
    Polynomial.monom (a ^ s) r"
proof (rule poly_ext)
  fix x
  have ev: "insertion (\<lambda>i. if i = 0 then x else a)
      (MPoly_Type.monom (green_monom_index (r,s)) 1) = x ^ r * a ^ s"
    using green_monom_eval[of "\<lambda>i. if i = 0 then x else a" r s]
    by simp
  show "poly (specialize_second a (MPoly_Type.monom (green_monom_index (r,s)) 1)) x =
      poly (Polynomial.monom (a^s) r) x"
    by (simp only: poly_specialize_second ev poly_monom; simp add: mult.commute)
qed

lemma green_quadratic_integer_monom_derivative:
  assumes c: "green_quadratic_integer d c"
    and z: "green_quadratic_integer d z"
  shows "green_quadratic_integer d
    (poly ((pderiv ^^ j) (Polynomial.monom c r)) z)"
  using c z
proof (induction j arbitrary: c r)
  case 0
  then show ?case
    by (simp add: poly_monom green_quadratic_integer_mult
      green_quadratic_integer_power)
next
  case (Suc j)
  have c': "green_quadratic_integer d (of_nat r * c)"
    by (rule green_quadratic_integer_mult)
      (use Suc.prems in simp_all)
  have eq: "(pderiv ^^ Suc j) (Polynomial.monom c r) =
    (pderiv ^^ j) (Polynomial.monom (of_nat r * c) (r - 1))"
    by (simp del: funpow.simps add: funpow_Suc_right pderiv_monom)
  show ?case
    unfolding eq by (rule Suc.IH[OF c' Suc.prems(2)])
qed

definition green_row_value ::
    "nat \<times> nat \<Rightarrow> nat \<Rightarrow> complex \<times> complex \<Rightarrow> complex" where
  "green_row_value k j p = green_first_derivative j
    (MPoly_Type.monom (green_monom_index k) 1) p"

lemma green_row_entry_quadratic_integer:
  assumes z: "green_quadratic_integer d (fst p)"
    and w: "green_quadratic_integer d (snd p)"
  shows "green_quadratic_integer d
    (green_first_derivative j
      (MPoly_Type.monom (green_monom_index (r,s)) 1) p)"
proof -
  have cw: "green_quadratic_integer d ((snd p) ^ s)"
    by (rule green_quadratic_integer_power[OF w])
  show ?thesis
    by (simp only: green_first_derivative_specialize green_specialized_monom;
      rule green_quadratic_integer_monom_derivative[OF cw z])
qed

lemma green_lattice_coordinates_quadratic_integer:
  "green_quadratic_integer d
      (fst (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y)))"
  "green_quadratic_integer d
      (snd (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y)))"
proof -
  have base: "green_quadratic_integer d (of_nat x)" by simp
  have slope: "green_quadratic_integer d (cpx_sqrt d * of_nat y)"
    by (rule green_quadratic_integer_mult; simp)
  have left: "green_quadratic_integer d (of_nat x + cpx_sqrt d * of_nat y)"
    by (rule green_quadratic_integer_add[OF base slope])
  have neg: "green_quadratic_integer d (- (cpx_sqrt d * of_nat y))"
    by (rule green_quadratic_integer_minus[OF slope])
  have right: "green_quadratic_integer d (of_nat x - cpx_sqrt d * of_nat y)"
    unfolding diff_conv_add_uminus
    by (rule green_quadratic_integer_add[OF base neg])
  show "green_quadratic_integer d
      (fst (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y)))"
    using left by (simp add: diagonal_point_def)
  show "green_quadratic_integer d
      (snd (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y)))"
    using right by (simp add: diagonal_point_def)
qed

lemma green_lattice_row_entry_quadratic_integer:
  "green_quadratic_integer d
    (green_first_derivative j
      (MPoly_Type.monom (green_monom_index (r,s)) 1)
      (diagonal_point (cpx_sqrt d) (of_nat x, of_nat y)))"
  by (rule green_row_entry_quadratic_integer)
    (rule green_lattice_coordinates_quadratic_integer)+

lemma green_lattice_grid_row_quadratic_integer:
  assumes p: "p \<in> diagonal_grid (cpx_sqrt d) (natural_grid N)"
  shows "green_quadratic_integer d (green_row_value k j p)"
proof -
  obtain x y :: nat where eq:
      "p = diagonal_point (cpx_sqrt d) (of_nat x, of_nat y)"
    using p by (auto simp: diagonal_grid_def natural_grid_def)
  obtain r s where k: "k = (r,s)" by (cases k) auto
  show ?thesis
    unfolding eq k green_row_value_def
    by (rule green_lattice_row_entry_quadratic_integer)
qed

lemma green_gram_sum_square:
  fixes c :: "'k \<Rightarrow> real" and a :: "'k \<Rightarrow> int"
  shows "(\<Sum>k\<in>K. \<Sum>l\<in>K. c k * c l * real_of_int (a k * a l)) =
    (\<Sum>k\<in>K. c k * real_of_int (a k))^2"
  by (simp add: power2_eq_square sum_distrib_left sum_distrib_right
    algebra_simps)

definition green_gram_entry ::
  "int \<Rightarrow> 'i set \<Rightarrow> ('k \<Rightarrow> 'i \<Rightarrow> int \<times> int) \<Rightarrow>
    'k \<Rightarrow> 'k \<Rightarrow> int" where
  "green_gram_entry d I f k l =
    (\<Sum>i\<in>I. green_quad_coeff_pair d (f k i) (f l i))"

lemma green_gram_entry_sym:
  "green_gram_entry d I f k l = green_gram_entry d I f l k"
  by (simp add: green_gram_entry_def green_quad_coeff_pair_def ac_simps)

lemma green_gram_entry_trace:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
  shows "green_gram_entry d I f k l =
    (\<Sum>i\<in>I. green_quad_trace_pair d
      (green_quad_embed d (f k i)) (green_quad_embed d (f l i)))"
proof -
  have point: "2 * (fst (f k i) * fst (f l i) +
      abs d * snd (f k i) * snd (f l i)) =
      green_quad_trace_pair d
        (green_quad_embed d (f k i)) (green_quad_embed d (f l i))"
    for i
  proof -
    obtain a b where fk: "f k i = (a,b)" by (cases "f k i") auto
    obtain c e where fl: "f l i = (c,e)" by (cases "f l i") auto
    show ?thesis
      by (simp add: fk fl green_quad_trace_pair_embed[OF irrational])
  qed
  show ?thesis
    unfolding green_gram_entry_def green_quad_coeff_pair_def
    by (rule sum.cong) (use point in auto)
qed

lemma green_gram_entry_field_trace:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
  shows "of_int (green_gram_entry d I f k l) =
    (\<Sum>i\<in>I. green_quad_field_trace d
      (green_quad_embed d (f k i) *
        cnj (green_quad_embed d (f l i))))"
proof -
  have point: "of_int (green_quad_trace_pair d
      (green_quad_embed d (f k i)) (green_quad_embed d (f l i))) =
    green_quad_field_trace d
      (green_quad_embed d (f k i) *
        cnj (green_quad_embed d (f l i)))" for i
  proof -
    obtain a b where fk: "f k i = (a,b)" by (cases "f k i") auto
    obtain c e where fl: "f l i = (c,e)" by (cases "f l i") auto
    show ?thesis
      by (simp add: fk fl green_quad_trace_pair_as_field_trace[OF irrational])
  qed
  show ?thesis
    unfolding green_gram_entry_trace[OF irrational] of_int_sum
    by (rule sum.cong) (use point in auto)
qed

lemma green_gram_point_square:
  fixes c :: "'k \<Rightarrow> real" and f :: "'k \<Rightarrow> int \<times> int"
  shows "(\<Sum>k\<in>K. \<Sum>l\<in>K. c k * c l *
      real_of_int (2 * (fst (f k) * fst (f l) +
        abs d * snd (f k) * snd (f l)))) =
    2 * ((\<Sum>k\<in>K. c k * real_of_int (fst (f k)))^2 +
      real_of_int (abs d) *
        (\<Sum>k\<in>K. c k * real_of_int (snd (f k)))^2)"
  by (simp add: green_gram_sum_square[symmetric]
    sum.distrib sum_distrib_left sum_distrib_right algebra_simps)

definition green_gram_form ::
  "int \<Rightarrow> 'i set \<Rightarrow> ('k \<Rightarrow> 'i \<Rightarrow> int \<times> int) \<Rightarrow>
    'k set \<Rightarrow> ('k \<Rightarrow> real) \<Rightarrow> real" where
  "green_gram_form d I f K c =
    (\<Sum>k\<in>K. \<Sum>l\<in>K.
      c k * c l * real_of_int (green_gram_entry d I f k l))"

lemma green_gram_form_squares:
  assumes finiteI: "finite I" and finiteK: "finite K"
  shows "green_gram_form d I f K c =
    (\<Sum>i\<in>I. 2 * (
      (\<Sum>k\<in>K. c k * real_of_int (fst (f k i)))^2 +
      real_of_int (abs d) *
      (\<Sum>k\<in>K. c k * real_of_int (snd (f k i)))^2))"
proof -
  let ?h = "\<lambda>k l i. c k * c l *
    real_of_int (2 * (fst (f k i) * fst (f l i) +
      abs d * snd (f k i) * snd (f l i)))"
  have first: "green_gram_form d I f K c =
    (\<Sum>k\<in>K. \<Sum>l\<in>K. \<Sum>i\<in>I. ?h k l i)"
    by (simp only: green_gram_form_def green_gram_entry_def
      green_quad_coeff_pair_def
      of_int_sum sum_distrib_left)
  have swap1: "(\<Sum>k\<in>K. \<Sum>l\<in>K. \<Sum>i\<in>I. ?h k l i) =
    (\<Sum>k\<in>K. \<Sum>i\<in>I. \<Sum>l\<in>K. ?h k l i)"
  proof (rule sum.cong)
    show "K = K" by simp
    fix k assume "k \<in> K"
    show "(\<Sum>l\<in>K. \<Sum>i\<in>I. ?h k l i) =
      (\<Sum>i\<in>I. \<Sum>l\<in>K. ?h k l i)"
      by (rule sum.swap)
  qed
  have swap2: "(\<Sum>k\<in>K. \<Sum>i\<in>I. \<Sum>l\<in>K. ?h k l i) =
    (\<Sum>i\<in>I. \<Sum>k\<in>K. \<Sum>l\<in>K. ?h k l i)"
    by (rule sum.swap)
  have point: "(\<Sum>k\<in>K. \<Sum>l\<in>K. ?h k l i) =
    2 * ((\<Sum>k\<in>K. c k * real_of_int (fst (f k i)))^2 +
      real_of_int (abs d) *
      (\<Sum>k\<in>K. c k * real_of_int (snd (f k i)))^2)" for i
    by (rule green_gram_point_square)
  show ?thesis
    using first swap1 swap2 point by simp
qed

lemma green_gram_linear_eval:
  fixes c :: "'k \<Rightarrow> real" and f :: "'k \<Rightarrow> int \<times> int"
  shows "(\<Sum>k\<in>K. of_real (c k) * green_quad_embed d (f k)) =
    of_real (\<Sum>k\<in>K. c k * real_of_int (fst (f k))) +
    of_real (\<Sum>k\<in>K. c k * real_of_int (snd (f k))) * cpx_sqrt d"
  by (simp add: green_quad_embed_def sum.distrib sum_distrib_left
    algebra_simps)

lemma green_gram_form_positive:
  assumes finiteI: "finite I" and finiteK: "finite K"
    and dnz: "d \<noteq> 0"
    and independent: "\<And>c::'k \<Rightarrow> real.
      (\<And>i. i \<in> I \<Longrightarrow>
        (\<Sum>k\<in>K. of_real (c k) * green_quad_embed d (f k i)) = 0)
      \<Longrightarrow> (\<forall>k\<in>K. c k = 0)"
    and nonzero: "\<exists>k\<in>K. c k \<noteq> 0"
  shows "0 < green_gram_form d I f K c"
proof -
  let ?A = "\<lambda>i. \<Sum>k\<in>K. c k * real_of_int (fst (f k i))"
  let ?B = "\<lambda>i. \<Sum>k\<in>K. c k * real_of_int (snd (f k i))"
  let ?term = "\<lambda>i. 2 * (?A i^2 + real_of_int (abs d) * ?B i^2)"
  have exists: "\<exists>i\<in>I. ?A i \<noteq> 0 \<or> ?B i \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>i\<in>I. ?A i \<noteq> 0 \<or> ?B i \<noteq> 0)"
    then have zero: "?A i = 0" "?B i = 0" if "i \<in> I" for i
      using that by auto
    have relation: "(\<Sum>k\<in>K.
      of_real (c k) * green_quad_embed d (f k i)) = 0"
      if "i \<in> I" for i
      using green_gram_linear_eval[where c=c and K=K and d=d
        and f="\<lambda>k. f k i"] zero[OF that]
      by simp
    have "\<forall>k\<in>K. c k = 0" by (rule independent[OF relation])
    with nonzero show False by blast
  qed
  obtain i where i: "i \<in> I" "?A i \<noteq> 0 \<or> ?B i \<noteq> 0"
    using exists by blast
  have term_nonneg: "0 \<le> ?term j" for j by simp
  have term_pos: "0 < ?term i"
  proof (cases "?A i = 0")
    case True
    then have "?B i \<noteq> 0" using i by simp
    then show ?thesis using True dnz by simp
  next
    case False
    then have "0 < ?A i^2" by simp
    moreover have "0 \<le> real_of_int (abs d) * ?B i^2" by simp
    ultimately have "0 < ?A i^2 + real_of_int (abs d) * ?B i^2"
      by linarith
    then show ?thesis by simp
  qed
  have "0 < (\<Sum>j\<in>I. ?term j)"
  proof (rule sum_pos2)
    show "finite I" by (rule finiteI)
    show "i \<in> I" by (rule i(1))
    show "0 < ?term i" by (rule term_pos)
    fix j assume "j \<in> I"
    show "0 \<le> ?term j" by (rule term_nonneg)
  qed
  then show ?thesis
    by (simp add: green_gram_form_squares[OF finiteI finiteK])
qed

definition green_row_gram_coeff ::
  "int \<Rightarrow> nat \<times> nat \<Rightarrow>
    (complex \<times> complex) \<times> nat \<Rightarrow> int \<times> int" where
  "green_row_gram_coeff d k ij =
    green_quad_coeff d (green_row_value k (snd ij) (fst ij))"

definition green_row_gram_form ::
  "int \<Rightarrow> (complex \<times> complex) set \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (nat \<times> nat \<Rightarrow> real) \<Rightarrow> real" where
  "green_row_gram_form d P J R S c =
    green_gram_form d (P \<times> {..<J}) (green_row_gram_coeff d)
      (green_row_indices R S) c"

lemma green_row_gram_form_positive:
  assumes finiteP: "finite P" and dnz: "d \<noteq> 0"
    and entries: "\<And>p j k. p \<in> P \<Longrightarrow> j < J \<Longrightarrow>
      k \<in> green_row_indices R S \<Longrightarrow>
      green_quadratic_integer d (green_row_value k j p)"
    and independent: "\<And>e::nat \<times> nat \<Rightarrow> complex.
      green_row_relation P J R S e \<Longrightarrow>
      (\<forall>k\<in>green_row_indices R S. e k = 0)"
    and nonzero: "\<exists>k\<in>green_row_indices R S. c k \<noteq> 0"
  shows "0 < green_row_gram_form d P J R S c"
proof -
  let ?K = "green_row_indices R S"
  let ?I = "P \<times> {..<J}"
  have finI: "finite ?I" using finiteP by simp
  have finK: "finite ?K" by simp
  have independent_real: "\<forall>k\<in>?K. e k = 0"
    if zero: "\<And>ij. ij \<in> ?I \<Longrightarrow>
      (\<Sum>k\<in>?K. of_real (e k) *
        green_quad_embed d (green_row_gram_coeff d k ij)) = 0"
    for e :: "nat \<times> nat \<Rightarrow> real"
  proof -
    have relation: "green_row_relation P J R S (\<lambda>k. of_real (e k))"
      unfolding green_row_relation_def
    proof (intro ballI allI impI)
      fix p j
      assume p: "p \<in> P" and j: "j < J"
      have coeff: "green_quad_embed d (green_row_gram_coeff d k (p,j)) =
        green_row_value k j p" if k: "k \<in> ?K" for k
        using green_quad_embed_coeff[OF entries[OF p j k]]
        by (simp add: green_row_gram_coeff_def)
      have zero': "(\<Sum>k\<in>?K. of_real (e k) *
        green_quad_embed d (green_row_gram_coeff d k (p,j))) = 0"
        by (rule zero) (use p j in auto)
      have eqsum: "(\<Sum>k\<in>?K. of_real (e k) *
        green_first_derivative j
          (MPoly_Type.monom (green_monom_index k) 1) p) =
        (\<Sum>k\<in>?K. of_real (e k) *
          green_quad_embed d (green_row_gram_coeff d k (p,j)))"
      proof (rule sum.cong)
        show "?K = ?K" by simp
        fix k assume k: "k \<in> ?K"
        show "of_real (e k) * green_first_derivative j
            (MPoly_Type.monom (green_monom_index k) 1) p =
          of_real (e k) * green_quad_embed d
            (green_row_gram_coeff d k (p,j))"
          using coeff[OF k] by (simp add: green_row_value_def)
      qed
      show "(\<Sum>k\<in>?K. of_real (e k) *
        green_first_derivative j
          (MPoly_Type.monom (green_monom_index k) 1) p) = 0"
        using eqsum zero' by simp
    qed
    have all: "\<forall>k\<in>?K. of_real (e k) = 0"
      using independent[OF relation] by simp
    then show ?thesis by simp
  qed
  show ?thesis
    unfolding green_row_gram_form_def
    by (rule green_gram_form_positive[OF finI finK dnz independent_real nonzero])
qed

context green_quadratic_character
begin

lemma green_paper_gram_form_positive:
  assumes even: "even cparam" and cparam: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and nonzero: "\<exists>k\<in>green_row_indices
      (green_X q cparam) (green_J q cparam). c k \<noteq> 0"
  shows "0 < green_row_gram_form d
    (diagonal_grid (cpx_sqrt d) (natural_grid (green_N q cparam)))
    (green_J q cparam) (green_X q cparam) (green_J q cparam) c"
proof -
  have finiteP: "finite (diagonal_grid (cpx_sqrt d)
      (natural_grid (green_N q cparam)))"
    by (simp add: diagonal_grid_def natural_grid_finite)
  have dnz: "d \<noteq> 0" using conductor_pos discriminant_abs by auto
  have entries: "green_quadratic_integer d (green_row_value k j p)"
    if "p \<in> diagonal_grid (cpx_sqrt d)
      (natural_grid (green_N q cparam))" for p j k
    by (rule green_lattice_grid_row_quadratic_integer[OF that])
  have independent: "\<forall>k\<in>green_row_indices
      (green_X q cparam) (green_J q cparam). e k = 0"
    if relation: "green_row_relation
      (diagonal_grid (cpx_sqrt d) (natural_grid (green_N q cparam)))
      (green_J q cparam) (green_X q cparam) (green_J q cparam) e"
    for e :: "nat \<times> nat \<Rightarrow> complex"
    using green_paper_rows_independent[OF even cparam large relation]
    by blast
  show ?thesis
    by (rule green_row_gram_form_positive[OF finiteP dnz _ _ nonzero])
      (use entries independent in auto)
qed

end

end
