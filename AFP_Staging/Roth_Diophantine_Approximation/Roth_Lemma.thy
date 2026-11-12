theory Roth_Lemma
  imports
    Det_Factor_Bounds
begin

lemma roth_taylor_support_vars:
  assumes tc: "roth_taylor_coeff a I P \<noteq> 0"
  shows "Poly_Mapping.keys I \<subseteq> vars P"
proof -
  have "Poly_Mapping.keys I \<subseteq> vars (roth_translate a P)"
    using tc by (auto simp: roth_taylor_coeff_key vars_def)
  then show ?thesis using roth_vars_translate_subset by blast
qed

lemma roth_index_extend_dimension:
  fixes P :: "rat mpoly"
  assumes pv: "vars P \<subseteq> {..<n}"
  shows "roth_index (Suc n) r a P = roth_index n r a P"
proof (cases "P=0")
  case True
  then show ?thesis by simp
next
  case False
  obtain I where ic: "roth_taylor_coeff a I P \<noteq> 0"
    and ie: "roth_index n r a P = ereal (roth_weight n r I)"
    using roth_index_attained[OF False, where m=n and r=r and a=a]
    by blast
  have ik: "Poly_Mapping.keys I \<subseteq> {..<n}"
    using roth_taylor_support_vars[OF ic] pv by blast
  have iw: "roth_weight (Suc n) r I = roth_weight n r I"
    by (rule roth_weight_extend_zero[OF ik])
  have le: "roth_index (Suc n) r a P \<le> roth_index n r a P"
    using roth_index_le_coeff[OF ic, of "Suc n" r] ie iw by simp
  obtain J where jc: "roth_taylor_coeff a J P \<noteq> 0"
    and je: "roth_index (Suc n) r a P =
      ereal (roth_weight (Suc n) r J)"
    using roth_index_attained[OF False, where m="Suc n" and r=r and a=a]
    by blast
  have jk: "Poly_Mapping.keys J \<subseteq> {..<n}"
    using roth_taylor_support_vars[OF jc] pv by blast
  have jw: "roth_weight (Suc n) r J = roth_weight n r J"
    by (rule roth_weight_extend_zero[OF jk])
  have ge: "roth_index n r a P \<le> roth_index (Suc n) r a P"
    using roth_index_le_coeff[OF jc, of n r] je jw by simp
  show ?thesis by (rule antisym[OF le ge])
qed

section \<open>One-variable index at an arbitrary coordinate\<close>

lemma roth_univariate_index_order_at:
  fixes p :: "rat poly" and r :: "nat \<Rightarrow> nat"
  assumes p: "p \<noteq> 0" and vm: "v<m" and rp: "r v > 0"
  shows "roth_index m r a (poly_to_mpoly v p) =
    ereal (real (Polynomial.order (a v) p) / real (r v))"
proof -
  let ?s = "pcompose p [:a v,1:]"
  let ?l = "Polynomial.order (a v) p"
  have snz: "?s \<noteq> 0"
    using p by (simp add: pcompose_eq_0_iff)
  have ord: "Polynomial.order 0 ?s = ?l"
    using roth_order_shift[OF p, of "a v"] .
  have low: "\<forall>k<?l. Polynomial.coeff ?s k = 0"
    and high: "Polynomial.coeff ?s ?l \<noteq> 0"
    using roth_order_zero_coeff[OF snz] ord by auto
  have tcl: "roth_taylor_coeff a
      (Poly_Mapping.single v ?l) (poly_to_mpoly v p) \<noteq> 0"
    using high by (simp add: roth_univariate_taylor_coeff)
  have w: "roth_weight m r (Poly_Mapping.single v ?l) =
    real ?l / real (r v)"
    by (rule roth_weight_single[OF vm])
  have ub: "roth_index m r a (poly_to_mpoly v p) \<le>
    ereal (real ?l / real (r v))"
    using roth_index_le_coeff[OF tcl, of m r] w by metis
  have pmp: "poly_to_mpoly v p \<noteq> 0"
    by (rule roth_poly_to_mpoly_nonzero[OF p])
  obtain I where tc: "roth_taylor_coeff a I (poly_to_mpoly v p) \<noteq> 0"
    and ieq: "roth_index m r a (poly_to_mpoly v p) =
      ereal (roth_weight m r I)"
    using roth_index_attained[OF pmp, where m=m and r=r and a=a]
    by blast
  have irep: "I = Poly_Mapping.single v (Poly_Mapping.lookup I v)"
    by (rule roth_univariate_taylor_support[OF tc])
  have kcoeff: "Polynomial.coeff ?s (Poly_Mapping.lookup I v) \<noteq> 0"
    using tc irep roth_univariate_taylor_coeff by metis
  have lk: "?l \<le> Poly_Mapping.lookup I v"
    using low kcoeff by (metis not_le_imp_less)
  have wI: "roth_weight m r I =
    real (Poly_Mapping.lookup I v) / real (r v)"
  proof -
    have "roth_weight m r I =
      roth_weight m r
        (Poly_Mapping.single v (Poly_Mapping.lookup I v))"
      by (rule arg_cong[OF irep])
    also have "... = real (Poly_Mapping.lookup I v) / real (r v)"
      by (rule roth_weight_single[OF vm])
    finally show ?thesis .
  qed
  have lb: "ereal (real ?l / real (r v)) \<le>
      roth_index m r a (poly_to_mpoly v p)"
    using ieq wI lk rp by (simp add: divide_right_mono)
  show ?thesis by (rule antisym[OF ub lb])
qed

lemma roth_univariate_index_bound_at:
  fixes P :: "rat mpoly" and r :: "nat \<Rightarrow> nat"
  assumes P: "P \<noteq> 0" and pv: "vars P \<subseteq> {v}"
    and vm: "v<m" and rp: "r v > 0"
    and deg: "degree (mpoly_to_poly v P) \<le> r v"
    and eta: "eta > 0"
    and h: "roth_proj_log_height P + real (r v) \<le>
      eta * real (r v) * roth_rat_log_height (a v)"
  shows "roth_index m r a P \<le> ereal eta"
proof -
  let ?p = "mpoly_to_poly v P"
  have pn: "?p \<noteq> 0"
    by (rule roth_mpoly_to_poly_nonzero[OF P pv])
  have peq: "poly_to_mpoly v ?p = P"
    by (rule mpoly_to_poly_inverse[OF pv])
  have rpos: "(0::real) < real (r v)" using rp by simp
  have posprod: "0 < eta * real (r v) * roth_rat_log_height (a v)"
    using h rpos roth_proj_log_height_nonneg[of P] by linarith
  have ep: "0 < eta * real (r v)" using eta rpos by simp
  have hp: "0 < roth_rat_log_height (a v)"
    using posprod ep by (auto simp: zero_less_mult_iff)
  have b: "real (Polynomial.order (a v) ?p) *
      roth_rat_log_height (a v) \<le>
    roth_proj_log_height P + real (degree ?p)"
    by (rule roth_univariate_mpoly_log_order_bound[OF P pv])
  have bd: "real (Polynomial.order (a v) ?p) *
      roth_rat_log_height (a v) \<le>
    eta * real (r v) * roth_rat_log_height (a v)"
    using b deg h by linarith
  have l: "real (Polynomial.order (a v) ?p) \<le> eta * real (r v)"
    using bd hp by (simp add: mult_le_cancel_right_pos)
  have ratio: "real (Polynomial.order (a v) ?p) / real (r v) \<le> eta"
    using l rpos by (simp add: pos_divide_le_eq)
  have io: "roth_index m r a (poly_to_mpoly v ?p) =
    ereal (real (Polynomial.order (a v) ?p) / real (r v))"
    by (rule roth_univariate_index_order_at)
      (use pn vm rp in auto)
  show ?thesis using io peq ratio by simp
qed


lemma roth_univariate_degree_of_box_at:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box (Suc n) r P"
  shows "degree (mpoly_to_poly n P) \<le> r n"
proof (rule degree_le, intro allI impI)
  fix i assume i: "r n < i"
  have outside: "Poly_Mapping.single n i \<notin>
      roth_exponent_box (Suc n) r"
    using i by (auto simp: roth_exponent_box_iff)
  show "Polynomial.coeff (mpoly_to_poly n P) i = 0"
    using roth_coeff_zero_outside_box[OF box outside] by simp
qed


lemma roth_univariate_index_bound_degree_at:
  fixes P :: "rat mpoly" and r :: "nat \<Rightarrow> nat"
  assumes P: "P \<noteq> 0" and pv: "vars P \<subseteq> {v}"
    and vm: "v<m" and rp: "r v > 0" and Dp: "D > 0"
    and deg: "degree (mpoly_to_poly v P) \<le> D"
    and eta: "eta > 0"
    and h: "roth_proj_log_height P + real D \<le>
      eta * real D * roth_rat_log_height (a v)"
  shows "roth_index m r a P \<le>
    ereal (eta * real D / real (r v))"
proof -
  let ?p = "mpoly_to_poly v P"
  have pn: "?p \<noteq> 0"
    by (rule roth_mpoly_to_poly_nonzero[OF P pv])
  have peq: "poly_to_mpoly v ?p = P"
    by (rule mpoly_to_poly_inverse[OF pv])
  have rpos: "(0::real) < real (r v)" using rp by simp
  have posprod: "0 < eta * real D * roth_rat_log_height (a v)"
    using h Dp roth_proj_log_height_nonneg[of P] by linarith
  have ep: "0 < eta * real D" using eta Dp by simp
  have hp: "0 < roth_rat_log_height (a v)"
    using posprod ep by (auto simp: zero_less_mult_iff)
  have b: "real (Polynomial.order (a v) ?p) *
      roth_rat_log_height (a v) \<le>
    roth_proj_log_height P + real (degree ?p)"
    by (rule roth_univariate_mpoly_log_order_bound[OF P pv])
  have bd: "real (Polynomial.order (a v) ?p) *
      roth_rat_log_height (a v) \<le>
    eta * real D * roth_rat_log_height (a v)"
    using b deg h by linarith
  have l: "real (Polynomial.order (a v) ?p) \<le> eta * real D"
    using bd hp by (simp add: mult_le_cancel_right_pos)
  have ratio: "real (Polynomial.order (a v) ?p) / real (r v) \<le>
      eta * real D / real (r v)"
    using l rpos by (simp add: divide_right_mono)
  have io: "roth_index m r a (poly_to_mpoly v ?p) =
    ereal (real (Polynomial.order (a v) ?p) / real (r v))"
    by (rule roth_univariate_index_order_at)
      (use pn vm rp in auto)
  show ?thesis using io peq ratio by simp
qed

lemma roth_weight_scale:
  assumes kp: "0 < k"
  shows "roth_weight m r I =
    real k * roth_weight m (\<lambda>v. k*r v) I"
proof -
  have eq: "real (Poly_Mapping.lookup I v) / real (r v) =
      real k * (real (Poly_Mapping.lookup I v) / real (k*r v))"
    for v
  proof (cases "r v=0")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using kp
      by (simp add: field_simps)
  qed
  have "roth_weight m r I =
    (\<Sum>v<m. real (Poly_Mapping.lookup I v) / real (r v))"
    by (simp add: roth_weight_def)
  also have "... =
    (\<Sum>v<m. real k *
      (real (Poly_Mapping.lookup I v) / real (k*r v)))"
    by (rule sum.cong) (use eq in auto)
  also have "... = real k * roth_weight m (\<lambda>v. k*r v) I"
    by (simp add: roth_weight_def sum_distrib_left)
  finally show ?thesis .
qed

lemma roth_index_scale_bound:
  fixes P :: "rat mpoly"
  assumes kp: "0 < k" and pn: "P \<noteq> 0"
    and bound: "roth_index m (\<lambda>v. k*r v) a P \<le> ereal C"
  shows "roth_index m r a P \<le> ereal (real k * C)"
proof -
  obtain I where tc: "roth_taylor_coeff a I P \<noteq> 0"
    and ie: "roth_index m (\<lambda>v. k*r v) a P =
      ereal (roth_weight m (\<lambda>v. k*r v) I)"
    using roth_index_attained[OF pn, where m=m and r="\<lambda>v. k*r v"
      and a=a] by blast
  have w: "roth_weight m (\<lambda>v. k*r v) I \<le> C"
    using ie bound by simp
  have ml: "real k * roth_weight m (\<lambda>v. k*r v) I \<le>
    real k * C"
    by (rule mult_left_mono[OF w]) simp
  have wr: "roth_weight m r I \<le> real k * C"
    using roth_weight_scale[OF kp, of m r I] ml by simp
  have le: "roth_index m r a P \<le> ereal (roth_weight m r I)"
    by (rule roth_index_le_coeff[OF tc])
  show ?thesis by (rule order_trans[OF le]) (use wr in simp)
qed

lemma roth_sigma_recursion:
  "((eta::real)^2)^(2^n) = eta^(2^(Suc n))"
  by (simp add: power_mult power_Suc mult.commute)

lemma roth_sigma_le_eta:
  fixes eta :: real
  assumes e0: "0 \<le> eta" and e1: "eta \<le> 1"
  shows "eta^(2^n) \<le> eta"
proof -
  have "eta^(2^n) \<le> eta^1"
    by (rule power_decreasing) (use e0 e1 in auto)
  then show ?thesis by simp
qed

lemma roth_sigma_le_eta_sq:
  fixes eta :: real
  assumes e0: "0 \<le> eta" and e1: "eta \<le> 1"
  shows "eta^(2^(Suc n)) \<le> eta^2"
  by (rule power_decreasing)
    (use e0 e1 in auto)

lemma roth_ratio_halving:
  fixes r :: "nat \<Rightarrow> nat" and sigma :: real
  assumes ratio: "\<And>v. Suc v<m \<Longrightarrow>
      real (r (Suc v)) \<le> sigma * real (r v)"
    and sb: "sigma \<le> 1/2"
    and vm: "Suc v<m"
  shows "2 * r (Suc v) \<le> r v"
proof -
  have "real (r (Suc v)) \<le> sigma * real (r v)"
    by (rule ratio[OF vm])
  also have "... \<le> (1/2) * real (r v)"
    by (rule mult_right_mono[OF sb]) simp
  finally show ?thesis by linarith
qed

lemma roth_ratio_divide:
  fixes r :: "nat \<Rightarrow> nat" and sigma :: real
  assumes rp: "0 < r n"
    and ratio: "real (r (Suc n)) \<le> sigma * real (r n)"
  shows "real (r (Suc n)) / real (r n) \<le> sigma"
  using rp ratio by (simp add: pos_divide_le_eq)

lemma roth_cancel_fact:
  assumes q: "real k * t^2 / (2 * real m) \<le>
    2 * real k * real m * eta^2"
    and kp: "0<k"
  shows "t^2 / (2 * real m) \<le> 2 * real m * eta^2"
proof -
  have e1: "real k * t^2 / (2 * real m) =
    real k * (t^2 / (2 * real m))"
    by (simp add: times_divide_eq_left mult.commute)
  have e2: "2 * real k * real m * eta^2 =
    real k * (2 * real m * eta^2)"
    by (simp add: algebra_simps)
  have fac: "real k * (t^2 / (2 * real m)) \<le>
    real k * (2 * real m * eta^2)"
    using q e1 e2 by metis
  have kpos: "(0::real) < real k" using kp by simp
  show ?thesis by (rule mult_left_le_imp_le[OF fac kpos])
qed

lemma roth_sq_fact:
  assumes mp: "0 < m"
    and q: "t^2 / (2 * real m) \<le> 2 * real m * eta^2"
  shows "t^2 \<le> (2 * real m * eta)^2"
  using mp q by (simp add: pos_divide_le_eq
      power2_eq_square algebra_simps)

lemma roth_final_index_arith:
  fixes t u l rho sigma eta :: real
  assumes kp: "0 < k" and mp: "0 < m" and ep: "0 \<le> eta"
    and ub: "u \<le> 2 * real k * real (m-1) * eta^2"
    and lb: "l \<le> real k * sigma"
    and rb: "rho \<le> sigma" and sb: "sigma \<le> eta^2"
    and qb: "real k * t^2 / (2 * real m) \<le> u+l+real k*rho"
  shows "t \<le> 2 * real m * eta"
proof -
  have k0: "(0::real) \<le> real k" by simp
  have kl: "real k * sigma \<le> real k * eta^2"
    by (rule mult_left_mono[OF sb k0])
  have kr: "real k * rho \<le> real k * sigma"
    by (rule mult_left_mono[OF rb k0])
  have ar: "2 * real k * real (m-1) * eta^2 +
      2 * real k * eta^2 = 2 * real k * real m * eta^2"
    using mp by (simp add: of_nat_diff algebra_simps)
  have bv: "u+l+real k*rho \<le> 2 * real k * real m * eta^2"
    using ub lb kr kl ar by linarith
  have q: "real k * t^2 / (2 * real m) \<le>
      2 * real k * real m * eta^2"
    using qb bv by linarith
  have q': "t^2 / (2 * real m) \<le> 2 * real m * eta^2"
    by (rule roth_cancel_fact[OF q kp])
  have sq: "t^2 \<le> (2 * real m * eta)^2"
    by (rule roth_sq_fact[OF mp q'])
  show ?thesis by (rule power2_le_imp_le[OF sq])
    (use ep in auto)
qed

lemma roth_ratio_scale:
  fixes r :: "nat \<Rightarrow> nat" and sigma :: real
  assumes ratio: "real (r (Suc v)) \<le> sigma * real (r v)"
  shows "real (k * r (Suc v)) \<le> sigma * real (k * r v)"
proof -
  have "real k * real (r (Suc v)) \<le>
    real k * (sigma * real (r v))"
    by (rule mult_left_mono[OF ratio]) simp
  then show ?thesis by (simp add: mult.commute mult.left_commute)
qed

lemma roth_height_transfer_sigma:
  fixes hF hP sigma H r0 rv :: real
  assumes fb: "hF \<le> real k * (hP + 4*r0)"
    and hb: "hP + 4*real (Suc n)*r0 \<le> sigma*rv*H"
  shows "hF + 4*real n*real k*r0 \<le> sigma*(real k*rv)*H"
proof -
  have f: "hF + 4*real n*real k*r0 \<le>
    real k * (hP + 4*real (Suc n)*r0)"
    using fb by (simp add: algebra_simps)
  have g: "real k * (hP + 4*real (Suc n)*r0) \<le>
    real k * (sigma*rv*H)"
    by (rule mult_left_mono[OF hb]) simp
  show ?thesis using f g by (simp add: algebra_simps)
qed

lemma roth_height_transfer_last:
  fixes hF hP sigma H r0 rv D :: real
  assumes d0: "0 \<le> D" and d: "D \<le> 4*real n*r0"
    and fb: "hF \<le> real k * (hP + 4*r0)"
    and hb: "hP + 4*real (Suc n)*r0 \<le> sigma*rv*H"
  shows "hF + real k*D \<le> sigma*(real k*rv)*H"
proof -
  have k0: "(0::real) \<le> real k" by simp
  have f: "hF + real k*D \<le>
    real k * (hP + 4*r0 + D)"
    using fb by (simp add: algebra_simps)
  have h: "hP + 4*r0 + D \<le>
    hP + 4*real (Suc n)*r0"
    using d by (simp add: algebra_simps)
  have g: "real k*(hP + 4*r0 + D) \<le>
    real k*(hP + 4*real (Suc n)*r0)"
    by (rule mult_left_mono[OF h k0])
  have z: "real k*(hP + 4*real (Suc n)*r0) \<le>
    real k*(sigma*rv*H)"
    by (rule mult_left_mono[OF hb k0])
  show ?thesis using f g z by (simp add: algebra_simps)
qed

lemma roth_rates_le_first:
  fixes r :: "nat \<Rightarrow> nat"
  assumes half: "\<And>v. Suc v < m \<Longrightarrow> 2*r (Suc v) \<le> r v"
    and vm: "v<m"
  shows "r v \<le> r 0"
  using vm
proof (induction v)
  case 0
  then show ?case by simp
next
  case (Suc v)
  have vp: "v<m" using Suc.prems by simp
  have le: "r (Suc v) \<le> r v" using half[OF Suc.prems] by simp
  show ?case using le Suc.IH[OF vp] by linarith
qed

section \<open>Determinant factors with their quantitative bounds\<close>

lemma roth_index_real_nonzero:
  fixes P :: "rat mpoly"
  assumes pn: "P \<noteq> 0"
  shows "\<exists>t\<ge>0. roth_index m r a P = ereal t"
proof -
  obtain I where ie: "roth_index m r a P =
      ereal (roth_weight m r I)"
    using roth_index_attained[OF pn, where m=m and r=r and a=a]
    by blast
  show ?thesis using ie roth_weight_nonneg by blast
qed

lemma roth_factor_height_bounds:
  fixes U L :: "rat mpoly"
  assumes un: "U \<noteq> 0" and ln: "L \<noteq> 0"
    and disj: "vars U \<inter> vars L = {}"
  shows "roth_proj_log_height U \<le> roth_proj_log_height (U*L) \<and>
    roth_proj_log_height L \<le> roth_proj_log_height (U*L)"
proof -
  have hu: "roth_proj_log_height U \<le> roth_proj_log_height (U*L)"
    by (rule roth_proj_log_height_disjoint_factor_le[OF un ln disj])
  have dl: "vars L \<inter> vars U = {}" using disj by auto
  have hl: "roth_proj_log_height L \<le> roth_proj_log_height (U*L)"
    using roth_proj_log_height_disjoint_factor_le[OF ln un dl]
    by (simp add: mult.commute)
  show ?thesis using hu hl by simp
qed

theorem roth_lemma_structure:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box (Suc (Suc n)) r P"
    and nz: "P \<noteq> 0"
    and half: "\<And>v. Suc v < Suc (Suc n) \<Longrightarrow>
      2 * r (Suc v) \<le> r v"
    and rp: "\<And>v. v < Suc (Suc n) \<Longrightarrow> 0 < r v"
  shows "\<exists>k U L.
    0 < k \<and> k \<le> Suc (r (Suc n)) \<and>
    roth_poly_in_box (Suc n) (\<lambda>v. k*r v) U \<and>
    roth_poly_in_box (Suc (Suc n)) (\<lambda>v. k*r v) L \<and>
    vars U \<subseteq> {..<Suc n} \<and>
    vars L \<subseteq> {Suc n} \<and>
    U \<noteq> 0 \<and> L \<noteq> 0 \<and>
    roth_proj_log_height (U*L) \<le>
      real k * (roth_proj_log_height P + 4 * real (r 0)) \<and>
    ereal (real k *
      (real_of_ereal (roth_index (Suc (Suc n)) r a P))^2 /
        (2 * real (Suc (Suc n)))) \<le>
      roth_index (Suc (Suc n)) r a (U*L) +
        ereal (real k *
          (real (r (Suc n)) / real (r n)))"
proof -
  obtain k mu U L where kp: "0 < k"
    and kn: "k \<le> Suc (r (Suc n))"
    and row: "\<forall>i<k. Poly_Mapping.keys (mu i) \<subseteq> {..<Suc n} \<and>
      roth_total_order (Suc n) (mu i) \<le> i"
    and ub: "roth_poly_in_box (Suc n) (\<lambda>v. k*r v) U"
    and lb: "roth_poly_in_box (Suc (Suc n)) (\<lambda>v. k*r v) L"
    and uv: "vars U \<subseteq> {..<Suc n}"
    and lv: "vars L \<subseteq> {Suc n}"
    and un: "U \<noteq> 0" and ln: "L \<noteq> 0"
    and fac: "det (mat k k (\<lambda>(i,j).
      roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P)) = U * L"
    using roth_box_tensor_det_factors_bounded[OF box nz] by blast
  have hb: "roth_proj_log_height (U*L) \<le>
    real k * (roth_proj_log_height P + 4 * real (r 0))"
    unfolding fac[symmetric]
    by (rule roth_hasse_det_log_bound_sharp[OF box nz half])
      (use kn in auto)
  have ib: "ereal (real k *
      (real_of_ereal (roth_index (Suc (Suc n)) r a P))^2 /
        (2 * real (Suc (Suc n)))) \<le>
      roth_index (Suc (Suc n)) r a (U*L) +
        ereal (real k *
          (real (r (Suc n)) / real (r n)))"
    unfolding fac[symmetric]
    by (rule roth_tensor_det_index_quadratic_box)
      (use box nz half rp kn row in auto)
  show ?thesis using kp kn ub lb uv lv un ln hb ib
    by (intro exI[where x=k] exI[where x=U]
      exI[where x=L]) auto
qed

section \<open>Roth's lemma for rational points\<close>

lemma roth_lemma_base:
  fixes P :: "rat mpoly" and eta :: real
  assumes pn: "P \<noteq> 0"
    and box: "roth_poly_in_box 1 r P"
    and rp: "0 < r 0" and ep: "0 < eta"
    and h: "roth_proj_log_height P + 4 * real (r 0) \<le>
      eta * real (r 0) * roth_rat_log_height (a 0)"
  shows "roth_index 1 r a P \<le> ereal (2 * eta)"
proof -
  have pv: "vars P \<subseteq> {0}"
    using roth_box_vars[OF box] by auto
  have box0: "roth_poly_in_box (Suc 0) r P"
    using box by simp
  have deg: "degree (mpoly_to_poly 0 P) \<le> r 0"
    by (rule roth_univariate_degree_of_box_at[OF box0])
  have hh: "roth_proj_log_height P + real (r 0) \<le>
      eta * real (r 0) * roth_rat_log_height (a 0)"
    using h by linarith
  have ib: "roth_index 1 r a P \<le> ereal eta"
    by (rule roth_univariate_index_bound_at[where v=0])
      (use pn pv rp deg ep hh in auto)
  have e2: "eta \<le> 2*eta" using ep by linarith
  show ?thesis by (rule order_trans[OF ib]) (use e2 in simp)
qed

theorem roth_lemma_aux:
  fixes P :: "rat mpoly" and eta :: real
  assumes pn: "P \<noteq> 0"
    and box: "roth_poly_in_box (Suc n) r P"
    and rp: "\<And>v. v < Suc n \<Longrightarrow> 0 < r v"
    and ep: "0 < eta" and eb: "eta \<le> 1/2"
    and ratio: "\<And>v. Suc v < Suc n \<Longrightarrow>
      real (r (Suc v)) \<le> eta^(2^n) * real (r v)"
    and height: "\<And>v. v < Suc n \<Longrightarrow>
      roth_proj_log_height P + 4*real (Suc n)*real (r 0) \<le>
        eta^(2^n) * real (r v) * roth_rat_log_height (a v)"
  shows "roth_index (Suc n) r a P \<le>
    ereal (2*real (Suc n)*eta)"
  using assms
proof (induction n arbitrary: P r a eta)
  case 0
  note hyp = this
  have "roth_index 1 r a P \<le> ereal (2*eta)"
    by (rule roth_lemma_base) (use hyp in auto)
  then show ?case by simp
next
  case (Suc n)
  let ?sigma = "eta^(2^(Suc n))"
  let ?m = "Suc (Suc n)"
  note pn = Suc.prems(1)
  note box = Suc.prems(2)
  note rp = Suc.prems(3)
  note ep = Suc.prems(4)
  note eb = Suc.prems(5)
  note ratio = Suc.prems(6)
  note height = Suc.prems(7)
  have sigma_pos: "0 < ?sigma" using ep by simp
  have sigma_sq: "?sigma \<le> eta^2"
    by (rule roth_sigma_le_eta_sq) (use ep eb in auto)
  have eta_one: "eta \<le> 1" using eb by linarith
  have sigma_eta: "?sigma \<le> eta"
    by (rule roth_sigma_le_eta) (use ep eta_one in auto)
  have sigma_half: "?sigma \<le> 1/2"
    using sigma_eta eb by linarith
  have half: "2*r (Suc v) \<le> r v" if "Suc v < ?m" for v
    by (rule roth_ratio_halving[where sigma="?sigma" and m="?m"])
      (use ratio sigma_half that in auto)
  obtain k U L where kp: "0 < k"
    and kn: "k \<le> Suc (r (Suc n))"
    and ub: "roth_poly_in_box (Suc n) (\<lambda>v. k*r v) U"
    and lb: "roth_poly_in_box ?m (\<lambda>v. k*r v) L"
    and uv: "vars U \<subseteq> {..<Suc n}"
    and lv: "vars L \<subseteq> {Suc n}"
    and un: "U \<noteq> 0" and ln: "L \<noteq> 0"
    and hb: "roth_proj_log_height (U*L) \<le>
      real k * (roth_proj_log_height P + 4 * real (r 0))"
    and ib: "ereal (real k *
      (real_of_ereal (roth_index ?m r a P))^2 /
        (2 * real ?m)) \<le>
      roth_index ?m r a (U*L) +
        ereal (real k * (real (r (Suc n)) / real (r n)))"
    using roth_lemma_structure[OF box pn half rp] by blast
  have disj: "vars U \<inter> vars L = {}" using uv lv by auto
  have fh: "roth_proj_log_height U \<le>
      real k * (roth_proj_log_height P + 4*real (r 0))"
    using roth_factor_height_bounds[OF un ln disj] hb by linarith
  have lh: "roth_proj_log_height L \<le>
      real k * (roth_proj_log_height P + 4*real (r 0))"
    using roth_factor_height_bounds[OF un ln disj] hb by linarith
  have eta2_pos: "0 < eta^2" using ep by simp
  have eta2_le_eta: "eta^2 \<le> eta"
  proof -
    have "eta^2 \<le> eta^1"
      by (rule power_decreasing) (use ep eta_one in auto)
    then show ?thesis by simp
  qed
  have eta2_half: "eta^2 \<le> 1/2"
    using eta2_le_eta eb by linarith
  have left_ratio: "real (k*r (Suc v)) \<le>
    (eta^2)^(2^n) * real (k*r v)" if "Suc v < Suc n" for v
  proof -
    have cv: "Suc v < ?m" using that by simp
    have "real (k*r (Suc v)) \<le> ?sigma * real (k*r v)"
      by (rule roth_ratio_scale[OF ratio[OF cv]])
    then show ?thesis by (simp add: roth_sigma_recursion)
  qed
  have left_height:
    "roth_proj_log_height U +
      4*real (Suc n)*real (k*r 0) \<le>
      (eta^2)^(2^n) * real (k*r v) *
        roth_rat_log_height (a v)" if "v<Suc n" for v
  proof -
    have hv: "roth_proj_log_height P +
      4*real ?m*real (r 0) \<le>
      ?sigma * real (r v) * roth_rat_log_height (a v)"
      by (rule height) (use that in simp)
    have tr: "roth_proj_log_height U +
      4*real (Suc n)*real k*real (r 0) \<le>
      ?sigma*(real k*real (r v))*roth_rat_log_height (a v)"
      by (rule roth_height_transfer_sigma[OF fh hv])
    show ?thesis using tr by (simp add: roth_sigma_recursion algebra_simps)
  qed
  have left_rp: "0 < k*r v" if "v<Suc n" for v
    using kp rp[of v] that by simp
  have UI: "roth_index (Suc n) (\<lambda>v. k*r v) a U \<le>
      ereal (2*real (Suc n)*(eta^2))"
    by (rule Suc.IH[OF un ub left_rp eta2_pos eta2_half
      left_ratio left_height])
  have UIs: "roth_index (Suc n) r a U \<le>
      ereal (real k*(2*real (Suc n)*(eta^2)))"
    by (rule roth_index_scale_bound[OF kp un UI])
  have UI_big: "roth_index ?m r a U \<le>
      ereal (2*real k*real (Suc n)*(eta^2))"
    using UIs roth_index_extend_dimension[OF uv, where r=r and a=a]
    by (simp add: algebra_simps)
  have rlast: "r (Suc n) \<le> r 0"
    by (rule roth_rates_le_first[where m="?m"])
      (use half in auto)
  have D_bound: "real (r (Suc n)) \<le>
      4*real (Suc n)*real (r 0)"
  proof -
    have d1: "(1::real) \<le> 4*real (Suc n)" by simp
    have d2: "1*real (r 0) \<le>
      (4*real (Suc n))*real (r 0)"
      by (rule mult_right_mono[OF d1]) simp
    show ?thesis using rlast d2 by linarith
  qed
  have hvlast: "roth_proj_log_height P +
      4*real ?m*real (r 0) \<le>
      ?sigma * real (r (Suc n)) *
        roth_rat_log_height (a (Suc n))"
    by (rule height) simp
  have last_height: "roth_proj_log_height L +
      real (k*r (Suc n)) \<le>
      ?sigma * real (k*r (Suc n)) *
        roth_rat_log_height (a (Suc n))"
  proof -
    have tr: "roth_proj_log_height L +
      real k*real (r (Suc n)) \<le>
      ?sigma*(real k*real (r (Suc n)))*
        roth_rat_log_height (a (Suc n))"
      by (rule roth_height_transfer_last[OF _ D_bound lh hvlast]) simp
    show ?thesis using tr by simp
  qed
  have last_deg: "degree (mpoly_to_poly (Suc n) L) \<le>
      k*r (Suc n)"
    using roth_univariate_degree_of_box_at[OF lb] by simp
  have last_rp: "0 < r (Suc n)" by (rule rp) simp
  have LI: "roth_index ?m r a L \<le> ereal (real k*?sigma)"
  proof -
    have ib: "roth_index ?m r a L \<le>
      ereal (?sigma*real (k*r (Suc n))/real (r (Suc n)))"
      by (rule roth_univariate_index_bound_degree_at
          [where v="Suc n" and D="k*r (Suc n)" and eta="?sigma"])
        (use ln lv last_rp last_deg sigma_pos last_height kp in auto)
    show ?thesis using ib last_rp by (simp add: algebra_simps)
  qed
  obtain t where t0: "0 \<le> t"
    and teq: "roth_index ?m r a P = ereal t"
    using roth_index_real_nonzero[OF pn, where m="Suc (Suc n)" and r=r and a=a]
    by blast
  obtain u where u0: "0 \<le> u"
    and ueq: "roth_index ?m r a U = ereal u"
    using roth_index_real_nonzero[OF un, where m="Suc (Suc n)" and r=r and a=a]
    by blast
  obtain l where l0: "0 \<le> l"
    and leq: "roth_index ?m r a L = ereal l"
    using roth_index_real_nonzero[OF ln, where m="Suc (Suc n)" and r=r and a=a]
    by blast
  have ubi: "u \<le> 2*real k*real (Suc n)*eta^2"
    using UI_big ueq by (simp add: algebra_simps)
  have lbi: "l \<le> real k*?sigma"
    using LI leq by simp
  have peq: "roth_index ?m r a (U*L) = ereal (u+l)"
    using roth_disjoint_index_mult[OF disj, where m="Suc (Suc n)" and r=r and a=a] ueq leq
    by simp
  have qi: "real k*t^2/(2*real ?m) \<le>
      u+l+real k*(real (r (Suc n))/real (r n))"
    using ib by (simp add: teq peq)
  have rpn: "0 < r n" by (rule rp) simp
  have rn: "real (r (Suc n)) \<le> ?sigma*real (r n)"
    by (rule ratio) simp
  have rho: "real (r (Suc n))/real (r n) \<le> ?sigma"
    by (rule roth_ratio_divide[OF rpn rn])
  have tb: "t \<le> 2*real ?m*eta"
    by (rule roth_final_index_arith
      [where m="?m" and sigma="?sigma" and
        rho="real (r (Suc n))/real (r n)"])
      (use kp ep ubi lbi rho sigma_sq qi in auto)
  show ?case using tb teq by simp
qed

theorem roth_lemma:
  fixes P :: "rat mpoly" and eta :: real
  assumes mp: "0 < m" and pn: "P \<noteq> 0"
    and box: "roth_poly_in_box m r P"
    and rp: "\<And>v. v<m \<Longrightarrow> 0<r v"
    and ep: "0<eta" and eb: "eta\<le>1/2"
    and ratio: "\<And>v. Suc v<m \<Longrightarrow>
      real (r (Suc v)) \<le> eta^(2^(m-1))*real (r v)"
    and height: "\<And>v. v<m \<Longrightarrow>
      roth_proj_log_height P + 4*real m*real (r 0) \<le>
        eta^(2^(m-1))*real (r v)*roth_rat_log_height (a v)"
  shows "roth_index m r a P \<le> ereal (2*real m*eta)"
proof -
  obtain n where meq: "m=Suc n" using mp by (cases m) auto
  have h: "roth_index (Suc n) r a P \<le>
      ereal (2*real (Suc n)*eta)"
    by (rule roth_lemma_aux[OF pn])
      (use meq box rp ep eb ratio height in auto)
  show ?thesis using h meq by simp
qed

lemma roth_proj_log_height_cast_bound:
  fixes Q :: "int mpoly"
  shows "roth_proj_log_height (replace_coeff of_int Q) \<le>
    ln (real (roth_int_coeff_sup Q))"
proof -
  have le: "roth_proj_height (replace_coeff of_int Q) \<le>
      roth_int_coeff_sup Q"
    by (rule roth_proj_height_cast)
  have lreal: "real (roth_proj_height (replace_coeff of_int Q)) \<le>
    real (roth_int_coeff_sup Q)" using le by simp
  have ppos: "0 < real (roth_proj_height (replace_coeff of_int Q))"
    using roth_proj_height_ge_one[of "replace_coeff of_int Q"] by simp
  show ?thesis unfolding roth_proj_log_height_def
    by (rule ln_mono[OF lreal ppos])
qed

lemma roth_cast_int_nonzero:
  fixes Q :: "int mpoly"
  assumes q: "Q \<noteq> 0"
  shows "(replace_coeff of_int Q :: rat mpoly) \<noteq> 0"
proof
  assume z: "(replace_coeff of_int Q :: rat mpoly) = 0"
  have eq: "replace_coeff of_int Q =
      MPoly_Type.smult (of_int 0::rat) (replace_coeff of_int Q)"
    using z by simp
  have "Q = MPoly_Type.smult (0::int) Q"
    by (rule roth_cast_smult_inject[OF eq])
  then show False using q by simp
qed

theorem roth_lemma_integer:
  fixes Q :: "int mpoly" and eta :: real
  assumes mp: "0 < m" and q: "Q \<noteq> 0"
    and box: "roth_poly_in_box m r Q"
    and rp: "\<And>v. v<m \<Longrightarrow> 0<r v"
    and ep: "0<eta" and eb: "eta\<le>1/2"
    and ratio: "\<And>v. Suc v<m \<Longrightarrow>
      real (r (Suc v)) \<le> eta^(2^(m-1))*real (r v)"
    and height: "\<And>v. v<m \<Longrightarrow>
      ln (real (roth_int_coeff_sup Q)) + 4*real m*real (r 0) \<le>
        eta^(2^(m-1))*real (r v)*roth_rat_log_height (a v)"
  shows "roth_index m r a (replace_coeff of_int Q) \<le>
    ereal (2*real m*eta)"
proof (rule roth_lemma[OF mp roth_cast_int_nonzero[OF q]])
  show "roth_poly_in_box m r (replace_coeff of_int Q :: rat mpoly)"
    using box by (simp add: roth_box_cast_iff)
  show "0 < r v" if "v<m" for v by (rule rp[OF that])
  show "0 < eta" by (rule ep)
  show "eta \<le> 1/2" by (rule eb)
  show "real (r (Suc v)) \<le> eta^(2^(m-1))*real (r v)"
    if "Suc v<m" for v by (rule ratio[OF that])
  show "roth_proj_log_height (replace_coeff of_int Q) +
      4*real m*real (r 0) \<le>
      eta^(2^(m-1))*real (r v)*roth_rat_log_height (a v)"
    if "v<m" for v
    using roth_proj_log_height_cast_bound[of Q] height[OF that]
    by linarith
qed

end
