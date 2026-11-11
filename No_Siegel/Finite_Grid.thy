theory Finite_Grid
  imports Schwartz_Zippel.Schwartz_Zippel
    Diophantine_Universal_Pairs.Substitutions
begin

text \<open>Green, Section 3 ("The Gram matrix is nonsingular"), paragraph after
  Lemma 3.1: the lattice points must satisfy the zero-counting hypothesis
  (2) of that lemma. We derive it from the AFP Schwartz-Zippel bound.\<close>

lemma finite_grid_zeros_functions:
  fixes P :: "'a::idom mpoly"
  assumes S: "finite S" "S \<noteq> {}"
    and P: "P \<noteq> 0" "vars P \<subseteq> {0, 1}" "total_degree P \<le> d"
  shows "card {f \<in> PiE_dflt {0::nat, 1} 0 (\<lambda>_. S). insertion f P = 0} \<le> d * card S"
proof -
  let ?T = "PiE_dflt {0::nat, 1} 0 (\<lambda>_. S)"
  let ?E = "{f \<in> ?T. insertion f P = 0}"
  have card_T: "card ?T = card S ^ 2"
    using S by (simp add: card_PiE_dflt power2_eq_square)
  have prob_bound:
    "measure_pmf.prob (Pi_pmf {0::nat, 1} 0 (\<lambda>_. pmf_of_set S))
       {f. insertion f P = 0} \<le> real d / real (card S)"
    by (rule schwartz_zippel) (use S P in auto)
  have finite_T: "finite ?T"
    using S by auto
  have nonempty_T: "?T \<noteq> {}"
    using S by simp
  have prob_eq:
    "measure_pmf.prob (Pi_pmf {0::nat, 1} 0 (\<lambda>_. pmf_of_set S))
       {f. insertion f P = 0} = real (card ?E) / real (card ?T)"
    using S finite_T nonempty_T
    by (simp add: Pi_pmf_of_set measure_pmf_of_set Int_def)
  have card_S_pos: "card S > 0"
    using S by (simp add: card_gt_0_iff)
  have "real (card ?E) \<le> real (d * card S)"
    using prob_bound prob_eq card_T card_S_pos
    by (simp add: field_simps power2_eq_square)
  then show ?thesis
    by (rule of_nat_le_iff[THEN iffD1])
qed


lemma finite_grid_zeros_pairs:
  fixes P :: "'a::idom mpoly"
  assumes S: "finite S" "S \<noteq> {}"
    and P: "P \<noteq> 0" "vars P \<subseteq> {0, 1}" "total_degree P \<le> d"
  shows "card {(x, y) \<in> S \<times> S.
      insertion (\<lambda>i. if i = 0 then x else if i = 1 then y else 0) P = 0}
    \<le> d * card S"
proof -
  let ?T = "PiE_dflt {0::nat, 1} 0 (\<lambda>_. S)"
  let ?E = "{f \<in> ?T. insertion f P = 0}"
  let ?h = "\<lambda>f. (f 0, f (Suc 0))"
  have canonical: "f = (\<lambda>i. if i = 0 then f 0 else if i = 1 then f (Suc 0) else 0)"
    if "f \<in> ?T" for f
    using that by (auto simp: PiE_dflt_def fun_eq_iff One_nat_def)
  have inj: "inj_on ?h ?E"
  proof (rule inj_onI)
    fix f g
    assume f: "f \<in> ?E" and g: "g \<in> ?E" and fg: "?h f = ?h g"
    have a: "f 0 = g 0" and b: "f 1 = g 1"
      using fg by auto
    show "f = g"
    proof (rule ext)
      fix i
      show "f i = g i"
      proof (cases "i = 0")
        case True
        then show ?thesis using a by simp
      next
        case False
        then have i0: "i \<noteq> 0" .
        show ?thesis
        proof (cases "i = 1")
          case True
          then show ?thesis using b by simp
        next
          case False
          have "f i = 0" "g i = 0"
            using f g i0 False by (auto simp: PiE_dflt_def)
          then show ?thesis by simp
        qed
      qed
    qed
  qed
  have image: "?h ` ?E = {(x, y) \<in> S \<times> S.
      insertion (\<lambda>i. if i = 0 then x else if i = 1 then y else 0) P = 0}"
  proof (intro equalityI subsetI)
    fix p
    assume "p \<in> ?h ` ?E"
    then obtain f where f: "f \<in> ?E" "p = ?h f" by auto
    have ev: "insertion (\<lambda>i. if i = 0 then f 0 else if i = 1 then f (Suc 0) else 0) P = 0"
      using canonical[of f] f by simp
    show "p \<in> {(x, y) \<in> S \<times> S.
        insertion (\<lambda>i. if i = 0 then x else if i = 1 then y else 0) P = 0}"
      using f ev by (auto simp: PiE_dflt_def One_nat_def)
  next
    fix p
    assume p: "p \<in> {(x, y) \<in> S \<times> S.
        insertion (\<lambda>i. if i = 0 then x else if i = 1 then y else 0) P = 0}"
    obtain x y where xy: "p = (x, y)" by (cases p) auto
    let ?f = "\<lambda>i. if i = 0 then x else if i = 1 then y else 0"
    have f_in: "?f \<in> ?E"
      using p xy by (auto simp: PiE_dflt_def)
    have h_eq: "p = ?h ?f"
      by (simp add: xy One_nat_def)
    show "p \<in> ?h ` ?E"
      using h_eq f_in by (rule image_eqI)
  qed
  have "card {(x, y) \<in> S \<times> S.
      insertion (\<lambda>i. if i = 0 then x else if i = 1 then y else 0) P = 0}
      = card (?h ` ?E)"
    by (simp only: image)
  also have "... = card ?E"
    by (rule card_image[OF inj])
  also have "... \<le> d * card S"
    by (rule finite_grid_zeros_functions[OF S P])
  finally show ?thesis .
qed


lemma linear_coordinates_inj:
  fixes a :: complex
  assumes "a \<noteq> 0"
  shows "inj (\<lambda>(x, y). (x + a * y, x - a * y))"
proof (rule injI)
  fix p q :: "complex \<times> complex"
  obtain x y where p: "p = (x, y)" by (cases p) auto
  obtain u v where q: "q = (u, v)" by (cases q) auto
  assume "(case p of (x, y) \<Rightarrow> (x + a * y, x - a * y)) =
          (case q of (x, y) \<Rightarrow> (x + a * y, x - a * y))"
  then have e1: "x + a * y = u + a * v"
    and e2: "x - a * y = u - a * v"
    by (simp_all add: p q)
  have "2 * x = (x + a * y) + (x - a * y)"
    by (simp add: algebra_simps)
  also have "... = (u + a * v) + (u - a * v)"
    using e1 e2 by simp
  also have "... = 2 * u"
    by (simp add: algebra_simps)
  finally have xu: "x = u" by simp
  have "a * y = a * v"
    using e1 xu by simp
  then have "y = v"
    using assms by simp
  then show "p = q" using p q xu by simp
qed

lemma mpoly_subst_power:
  "poly_subst f (p ^ n) = (poly_subst f (p::'a::comm_semiring_1 mpoly)) ^ n"
  by (induction n) (simp_all add: poly_subst_mult)

lemma mpoly_subst_comp:
  fixes f g :: "nat \<Rightarrow> 'a::comm_semiring_1 mpoly"
  shows "poly_subst f (poly_subst g P) = poly_subst (\<lambda>i. poly_subst f (g i)) P"
proof -
  have mid: "poly_subst f (poly_subst g P) =
     (\<Sum>t\<in>keys (mapping_of P). Const (MPoly_Type.coeff P t) *
        poly_subst_monom (\<lambda>i. poly_subst f (g i)) t)"
    unfolding poly_subst_alt[of g P]
    by (simp add: poly_subst_sum poly_subst_monom_alt poly_subst_prod mpoly_subst_power)
  show ?thesis using mid
    by (simp only: poly_subst_alt[of "\<lambda>i. poly_subst f (g i)" P])
qed

lemma mpoly_subst_linear_degree:
  fixes f :: "nat \<Rightarrow> 'a::comm_semiring_1 mpoly"
  assumes H: "\<And>i. i \<in> vars P \<Longrightarrow> total_degree (f i) \<le> 1"
  shows "total_degree (poly_subst f P) \<le> total_degree P"
proof -
  have monom_bound: "total_degree (poly_subst_monom f t) \<le> total_degree P"
    if t: "t \<in> keys (mapping_of P)" for t
  proof -
    have keys: "keys t \<subseteq> vars P"
      using t by (auto simp: vars_def)
    have "(\<Sum>i\<in>keys t. lookup t i * total_degree (f i)) \<le>
          (\<Sum>i\<in>keys t. lookup t i)"
      by (rule sum_mono) (use H keys in auto)
    moreover have "(\<Sum>i\<in>keys t. lookup t i) \<le> total_degree P"
      using t by (auto simp: total_degree.rep_eq)
    ultimately show ?thesis
      using total_degree_poly_subst_monom[of f t] by (simp add: mult.commute)
  qed
  have term_bound: "total_degree (Const (MPoly_Type.coeff P t) * poly_subst_monom f t)
      \<le> total_degree P"
    if t: "t \<in> keys (mapping_of P)" for t
    using total_degree_mult[of "Const (MPoly_Type.coeff P t)" "poly_subst_monom f t"]
      monom_bound[OF t] by simp
  have "total_degree (poly_subst f P) \<le>
      Max (insert 0 ((\<lambda>t. total_degree (Const (MPoly_Type.coeff P t) *
        poly_subst_monom f t)) ` keys (mapping_of P)))"
    unfolding poly_subst_alt by (rule total_degree_sum, simp)
  also have "... \<le> total_degree P"
    using term_bound by (auto intro!: Max.boundedI)
  finally show ?thesis .
qed

definition diagonal_subst :: "complex \<Rightarrow> nat \<Rightarrow> complex mpoly" where
  "diagonal_subst a i =
    (if i = 0 then Var 0 + Const a * Var 1
     else if i = 1 then Var 0 - Const a * Var 1 else Var i)"

definition diagonal_inverse :: "complex \<Rightarrow> nat \<Rightarrow> complex mpoly" where
  "diagonal_inverse a i =
    (if i = 0 then Const (1/2) * (Var 0 + Var 1)
     else if i = 1 then Const (1/(2*a)) * (Var 0 - Var 1) else Var i)"

lemma diagonal_subst_eval:
  "insertion f (poly_subst (diagonal_subst a) P) =
    insertion (\<lambda>i. if i = 0 then f 0 + a * f 1
                     else if i = 1 then f 0 - a * f 1 else f i) P"
proof -
  have eq: "(insertion f \<circ> diagonal_subst a) =
      (\<lambda>i. if i = 0 then f 0 + a * f 1
            else if i = 1 then f 0 - a * f 1 else f i)"
    by (rule ext) (simp add: diagonal_subst_def insertion_add insertion_mult insertion_diff)
  show ?thesis by (simp add: insertion_poly_subst eq)
qed

lemma grid_Const_mul: "Const (a::complex) * Const b = Const (a*b)"
  by (transfer, simp add: Const\<^sub>0_def mult_single)

lemma grid_Const_add: "Const (a::complex) + Const b = Const (a+b)"
  by (transfer, simp add: Const\<^sub>0_def single_add[symmetric])

lemma grid_Const_one: "Const (1::complex) = 1"
  by (transfer, simp add: Const\<^sub>0_def)

lemma grid_half_pair:
  fixes u v :: "complex mpoly"
  shows "Const (1/2) * (u+v) + Const (1/2) * (u-v) = u"
  by (simp add: algebra_simps mult_2 grid_Const_add grid_Const_one)

lemma grid_half_pair_diff:
  fixes u v :: "complex mpoly"
  shows "Const (1/2) * (u+v) - Const (1/2) * (u-v) = v"
  by (simp add: algebra_simps mult_2 grid_Const_add grid_Const_one)

lemma grid_Const_cancel_half:
  assumes "a \<noteq> (0::complex)"
  shows "Const a * Const (1/(2*a)) = Const (1/2)"
  using assms by (simp add: grid_Const_mul field_simps)

lemma diagonal_inverse_subst:
  assumes a: "a \<noteq> 0"
  shows "poly_subst (diagonal_inverse a) (diagonal_subst a i) = Var i"
proof -
  have scaled: "Const a * (Const (1/(2*a)) * (u-v)) = Const (1/2) * (u-v)"
    for u v :: "complex mpoly"
    by (simp add: mult.assoc[symmetric] grid_Const_cancel_half[OF a])
  show ?thesis
    by (cases "i = 0"; cases "i = 1")
       (simp_all add: diagonal_subst_def diagonal_inverse_def scaled
         grid_half_pair grid_half_pair_diff)
qed

lemma diagonal_subst_nonzero:
  assumes "a \<noteq> 0" "P \<noteq> (0::complex mpoly)"
  shows "poly_subst (diagonal_subst a) P \<noteq> 0"
proof
  assume z: "poly_subst (diagonal_subst a) P = 0"
  have comp_inv: "poly_subst (diagonal_inverse a) (poly_subst (diagonal_subst a) P) = P"
    by (simp add: mpoly_subst_comp diagonal_inverse_subst[OF assms(1)] poly_subst_id)
  show False using comp_inv z assms(2) by simp
qed

lemma diagonal_subst_degree: "total_degree (diagonal_subst a i) \<le> 1"
  by (cases "i = 0"; cases "i = 1")
     (auto simp: diagonal_subst_def
       intro!: order_trans[OF total_degree_add] order_trans[OF total_degree_diff]
         order_trans[OF total_degree_mult])

lemma diagonal_subst_vars:
  "vars (diagonal_subst a i) \<subseteq> {0, 1}" if "i \<in> {0, 1}"
proof -
  have plus: "vars (Var 0 + Const a * Var 1) \<subseteq> {0,1}"
    using vars_add[of "Var 0" "Const a * Var 1"]
      vars_mult[of "Const a" "Var 1"] by auto
  have minus: "vars (Var 0 - Const a * Var 1) \<subseteq> {0,1}"
    using vars_diff[of "Var 0" "Const a * Var 1"]
      vars_mult[of "Const a" "Var 1"] by auto
  show ?thesis using that plus minus by (auto simp: diagonal_subst_def)
qed

lemma diagonal_pullback_vars:
  assumes "vars P \<subseteq> {0,1}"
  shows "vars (poly_subst (diagonal_subst a) P) \<subseteq> {0,1}"
  using assms vars_poly_subst[of "diagonal_subst a" P] diagonal_subst_vars by blast

lemma diagonal_grid_zeros:
  fixes P :: "complex mpoly"
  assumes S: "finite S" "S \<noteq> {}"
    and a: "a \<noteq> 0"
    and P: "P \<noteq> 0" "vars P \<subseteq> {0,1}" "total_degree P \<le> d"
  shows "card {(x,y) \<in> S \<times> S.
      insertion (\<lambda>i. if i = 0 then x+a*y else if i = 1 then x-a*y else 0) P = 0}
    \<le> d * card S"
proof -
  let ?Q = "poly_subst (diagonal_subst a) P"
  have Q: "?Q \<noteq> 0" "vars ?Q \<subseteq> {0,1}" "total_degree ?Q \<le> d"
    using diagonal_subst_nonzero[OF a P(1)] diagonal_pullback_vars[OF P(2)]
      mpoly_subst_linear_degree[where f="diagonal_subst a" and P=P]
      diagonal_subst_degree P(3) by auto
  have eval: "insertion (\<lambda>i. if i = 0 then x else if i = 1 then y else 0) ?Q =
      insertion (\<lambda>i. if i = 0 then x+a*y else if i = 1 then x-a*y else 0) P"
    for x y
    unfolding diagonal_subst_eval
    by (rule arg_cong[where f="\<lambda>g. insertion g P"], rule ext)
       (auto split: if_splits)
  have eq: "{(x,y) \<in> S \<times> S.
        insertion (\<lambda>i. if i = 0 then x else if i = 1 then y else 0) ?Q = 0} =
      {(x,y) \<in> S \<times> S.
        insertion (\<lambda>i. if i = 0 then x+a*y else if i = 1 then x-a*y else 0) P = 0}"
    by (auto simp: eval)
  show ?thesis using finite_grid_zeros_pairs[OF S Q] by (simp only: eq)
qed

lemma diagonal_grid_point_zeros:
  fixes P :: "complex mpoly"
  assumes S: "finite S" "S \<noteq> {}"
    and a: "a \<noteq> 0"
    and P: "P \<noteq> 0" "vars P \<subseteq> {0,1}" "total_degree P \<le> d"
  shows "card {p \<in> (\<lambda>(x,y). (x+a*y,x-a*y)) ` (S \<times> S).
    insertion (\<lambda>i. if i = 0 then fst p else if i = 1 then snd p else 0) P = 0}
    \<le> d * card S"
proof -
  let ?E = "{(x,y) \<in> S \<times> S.
    insertion (\<lambda>i. if i = 0 then x+a*y else if i = 1 then x-a*y else 0) P = 0}"
  let ?h = "\<lambda>(x,y). (x+a*y,x-a*y)"
  have all_inj: "inj_on ?h UNIV"
    using linear_coordinates_inj[OF a] unfolding inj_def .
  have inj: "inj_on ?h ?E"
    by (rule inj_on_subset[OF all_inj]) simp
  have eval_h: "insertion (\<lambda>i. if i = 0 then fst (?h (x,y))
      else if i = 1 then snd (?h (x,y)) else 0) P =
      insertion (\<lambda>i. if i = 0 then x+a*y else if i = 1 then x-a*y else 0) P"
    for x y
    by (rule arg_cong[where f="\<lambda>g. insertion g P"], rule ext) simp
  have E': "?E = {q \<in> S \<times> S.
    insertion (\<lambda>i. if i = 0 then fst (?h q) else if i = 1 then snd (?h q) else 0) P = 0}"
  proof (rule set_eqI)
    fix q :: "complex \<times> complex"
    obtain x y where q: "q = (x,y)" by (cases q) auto
    show "q \<in> ?E \<longleftrightarrow> q \<in> {q \<in> S \<times> S.
      insertion (\<lambda>i. if i = 0 then fst (?h q) else if i = 1 then snd (?h q) else 0) P = 0}"
      by (simp add: q eval_h)
  qed
  have filter_image: "f ` {x \<in> A. Q (f x)} = {y \<in> f ` A. Q y}"
    for f :: "'x \<Rightarrow> 'y" and A Q
    by blast
  have image: "?h ` ?E = {p \<in> ?h ` (S \<times> S).
    insertion (\<lambda>i. if i = 0 then fst p else if i = 1 then snd p else 0) P = 0}"
    unfolding E' by (rule filter_image)
  have "card {p \<in> ?h ` (S \<times> S).
    insertion (\<lambda>i. if i = 0 then fst p else if i = 1 then snd p else 0) P = 0}
    = card (?h ` ?E)"
    by (simp only: image)
  also have "... = card ?E" by (rule card_image[OF inj])
  also have "... \<le> d * card S" by (rule diagonal_grid_zeros[OF S a P])
  finally show ?thesis .
qed

definition natural_grid :: "nat \<Rightarrow> complex set" where
  "natural_grid N = complex_of_nat ` {..<N}"

lemma natural_grid_card: "card (natural_grid N) = N"
  unfolding natural_grid_def by (simp add: card_image inj_on_def)

lemma natural_grid_finite: "finite (natural_grid N)"
  by (simp add: natural_grid_def)

lemma natural_grid_nonempty: "natural_grid N \<noteq> {}" if "N > 0"
  using that by (auto simp: natural_grid_def)

lemma natural_diagonal_grid_zeros:
  fixes P :: "complex mpoly"
  assumes N: "N > 0" and J: "N \<le> J" and a: "a \<noteq> 0"
    and P: "P \<noteq> 0" "vars P \<subseteq> {0,1}"
  shows "card {p \<in> (\<lambda>(x,y). (x+a*y,x-a*y)) ` (natural_grid N \<times> natural_grid N).
    insertion (\<lambda>i. if i = 0 then fst p else if i = 1 then snd p else 0) P = 0}
    \<le> J * total_degree P"
proof -
  have "card {p \<in> (\<lambda>(x,y). (x+a*y,x-a*y)) ` (natural_grid N \<times> natural_grid N).
    insertion (\<lambda>i. if i = 0 then fst p else if i = 1 then snd p else 0) P = 0}
    \<le> total_degree P * N"
    using diagonal_grid_point_zeros[OF natural_grid_finite natural_grid_nonempty[OF N]
      a P(1) P(2) le_refl]
    by (simp add: natural_grid_card)
  also have "... \<le> J * total_degree P"
    using J by (simp add: mult.commute mult_le_mono2)
  finally show ?thesis .
qed

definition pair_eval :: "'a::comm_semiring_1 mpoly \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a" where
  "pair_eval P p = insertion (\<lambda>i. if i = 0 then fst p else if i = 1 then snd p else 0) P"

definition diagonal_point :: "complex \<Rightarrow> complex \<times> complex \<Rightarrow> complex \<times> complex" where
  "diagonal_point a p = (fst p + a * snd p, fst p - a * snd p)"

definition diagonal_grid :: "complex \<Rightarrow> complex set \<Rightarrow> (complex \<times> complex) set" where
  "diagonal_grid a S = diagonal_point a ` (S \<times> S)"

lemma diagonal_point_eq: "diagonal_point a = (\<lambda>(x,y). (x+a*y,x-a*y))"
  by (rule ext) (auto simp: diagonal_point_def split: prod.splits)

lemma natural_diagonal_grid_bound:
  fixes P :: "complex mpoly"
  assumes N: "N > 0" and J: "N \<le> J" and a: "a \<noteq> 0"
    and P: "P \<noteq> 0" "vars P \<subseteq> {0,1}"
  shows "card {p \<in> diagonal_grid a (natural_grid N). pair_eval P p = 0}
    \<le> J * total_degree P"
  using natural_diagonal_grid_zeros[OF N J a P]
  by (simp add: diagonal_grid_def diagonal_point_eq pair_eval_def)

lemma diagonal_second_inj_on_rational_grid:
  fixes a :: complex
  assumes rat: "S \<subseteq> Rats" and irrational: "a \<notin> Rats"
  shows "inj_on (\<lambda>p. snd (diagonal_point a p)) (S \<times> S)"
proof (rule inj_onI)
  fix p q
  assume p: "p \<in> S \<times> S" and q: "q \<in> S \<times> S"
    and eq: "snd (diagonal_point a p) = snd (diagonal_point a q)"
  obtain x y where pp: "p = (x,y)" by (cases p) auto
  obtain u v where qq: "q = (u,v)" by (cases q) auto
  have xy: "x - a * y = u - a * v"
    using eq by (simp add: pp qq diagonal_point_def)
  have xr: "x \<in> Rats" and yr: "y \<in> Rats"
    and ur: "u \<in> Rats" and vr: "v \<in> Rats"
    using p q rat by (auto simp: pp qq)
  have yv: "y = v"
  proof (rule ccontr)
    assume ne: "y \<noteq> v"
    have "a * (y - v) = x - u" using xy by (simp add: algebra_simps)
    then have "a = (x - u) / (y - v)" using ne by (simp add: field_simps)
    then have "a \<in> Rats" using xr yr ur vr by simp
    with irrational show False by contradiction
  qed
  have "x = u" using xy yv by simp
  then show "p = q" using pp qq yv by simp
qed

lemma natural_diagonal_second_distinct:
  fixes a :: complex
  assumes "a \<notin> Rats"
  shows "inj_on (\<lambda>p. snd (diagonal_point a p))
    (natural_grid N \<times> natural_grid N)"
  by (rule diagonal_second_inj_on_rational_grid)
    (use assms in \<open>auto simp: natural_grid_def\<close>)

lemma diagonal_grid_second_distinct:
  fixes a :: complex
  assumes rat: "S \<subseteq> Rats" and irrational: "a \<notin> Rats"
  shows "inj_on snd (diagonal_grid a S)"
proof (rule inj_onI)
  fix p q
  assume p: "p \<in> diagonal_grid a S" and q: "q \<in> diagonal_grid a S"
    and eq: "snd p = snd q"
  obtain u where u: "u \<in> S \<times> S" "p = diagonal_point a u"
    using p by (auto simp: diagonal_grid_def)
  obtain v where v: "v \<in> S \<times> S" "q = diagonal_point a v"
    using q by (auto simp: diagonal_grid_def)
  have "u = v"
    using diagonal_second_inj_on_rational_grid[OF rat irrational]
      u v eq by (auto simp: inj_on_def)
  then show "p = q" using u v by simp
qed

lemma natural_diagonal_grid_second_distinct:
  fixes a :: complex
  assumes "a \<notin> Rats"
  shows "inj_on snd (diagonal_grid a (natural_grid N))"
  by (rule diagonal_grid_second_distinct)
    (use assms in \<open>auto simp: natural_grid_def\<close>)

end
