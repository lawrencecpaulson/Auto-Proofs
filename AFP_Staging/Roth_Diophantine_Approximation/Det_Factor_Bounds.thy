theory Det_Factor_Bounds
  imports Roth_Determinant_Bounds
begin

section \<open>Index bounds for determinants\<close>

lemma roth_index_sum_lower:
  fixes F :: "'b \<Rightarrow> rat mpoly"
  assumes fin: "finite S"
    and bd: "\<And>x. x\<in>S \<Longrightarrow> theta \<le> roth_index m r a (F x)"
  shows "theta \<le> roth_index m r a (\<Sum>x\<in>S. F x)"
  using fin bd
proof (induction S rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x S)
  have "theta \<le> min (roth_index m r a (F x)) (roth_index m r a (\<Sum>x\<in>S. F x))"
    using insert by auto
  also have "\<dots> \<le> roth_index m r a (\<Sum>x\<in>insert x S. F x)"
    using insert.hyps by (simp add: roth_index_add)
  finally show ?case .
qed

lemma roth_index_prod_lower:
  fixes F :: "'b \<Rightarrow> rat mpoly"
  assumes fin: "finite S"
  shows "(\<Sum>x\<in>S. roth_index m r a (F x)) \<le> roth_index m r a (\<Prod>x\<in>S. F x)"
  using fin
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: roth_index_nonneg)
next
  case (insert x S)
  have "roth_index m r a (F x) + (\<Sum>y\<in>S. roth_index m r a (F y)) \<le>
        roth_index m r a (F x) + roth_index m r a (\<Prod>y\<in>S. F y)"
    by (rule add_left_mono[OF insert.IH])
  also have "\<dots> \<le> roth_index m r a (F x * (\<Prod>y\<in>S. F y))"
    by (rule roth_index_mult)
  finally show ?case using insert.hyps by simp
qed

lemma roth_index_left_mult_lower:
  fixes P Q :: "rat mpoly"
  shows "roth_index m r a Q \<le> roth_index m r a (P*Q)"
proof -
  have "roth_index m r a Q \<le>
    roth_index m r a P + roth_index m r a Q"
    using add_right_mono[OF roth_index_nonneg[of m r a P]] by simp
  also have "\<dots> \<le> roth_index m r a (P*Q)"
    by (rule roth_index_mult)
  finally show ?thesis .
qed

lemma roth_index_det_lower:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
  assumes bd: "\<And>q. q permutes {..<k} \<Longrightarrow>
    theta \<le> (\<Sum>i<k. roth_index m r a (A i (q i)))"
  shows "theta \<le> roth_index m r a (det (mat k k (\<lambda>(i,j). A i j)))"
proof -
  let ?Q = "{q. q permutes {..<k}}"
  have fin: "finite ?Q" by (rule finite_permutations) simp
  have each: "theta \<le> roth_index m r a (signof q * (\<Prod>i<k. A i (q i)))" 
    if q: "q\<in>?Q" for q
  proof -
    have "theta \<le> (\<Sum>i<k. roth_index m r a (A i (q i)))"
      by (rule bd) (use q in auto)
    also have "\<dots> \<le> roth_index m r a (\<Prod>i<k. A i (q i))"
      by (rule roth_index_prod_lower) simp
    also have "\<dots> \<le> roth_index m r a (signof q * (\<Prod>i<k. A i (q i)))"
      by (rule roth_index_left_mult_lower)
    finally show ?thesis .
  qed
  show ?thesis unfolding roth_det_mat_expansion
    by (rule roth_index_sum_lower[OF fin each]) 
qed

lemma roth_index_hasse_lower:
  fixes P :: "rat mpoly"
  assumes ip: "roth_index m r a P = ereal t"
    and w: "roth_weight m r J \<le> L"
  shows "ereal (max 0 (t-L)) \<le> roth_index m r a (roth_hasse J P)"
proof -
  have h: "ereal (t - roth_weight m r J) \<le> roth_index m r a (roth_hasse J P)"
    using roth_index_hasse[of m r a P J] ip by simp
  have hl: "ereal (t-L) \<le> roth_index m r a (roth_hasse J P)"
    using ereal_le_le h w by auto
  show ?thesis using hl roth_index_nonneg[of m r a "roth_hasse J P"]
    by (simp add: zero_ereal_def)
qed

lemma roth_weight_single:
  assumes vm: "v<m"
  shows "roth_weight m r (Poly_Mapping.single v j) = j / (r v)"
proof -
  have eq: "(\<Sum>u<m. real (if v=u then j else 0) / real (r u)) =
    (\<Sum>u<m. if v=u then real j / real (r v) else 0)"
    by (rule sum.cong) auto
  show ?thesis using vm
    by (simp add: roth_weight_def lookup_single when_def eq)
qed

lemma roth_weight_prefix_bound:
  assumes rp: "0 < r n"
    and rb: "\<And>v. v<n \<Longrightarrow> r n \<le> r v"
  shows "roth_weight (Suc n) r J \<le> real (roth_total_order (Suc n) J) / real (r n)"
proof -
  have step: "real (Poly_Mapping.lookup J v) / real (r v) \<le>
    real (Poly_Mapping.lookup J v) / real (r n)"
    if vn: "v<Suc n" for v
    using that rb rp
    by (auto simp: less_Suc_eq divide_simps intro!: mult_mono)
  have "roth_weight (Suc n) r J =
    (\<Sum>v<Suc n. real (Poly_Mapping.lookup J v) / real (r v))"
    by (simp add: roth_weight_def)
  also have "\<dots> \<le>
    (\<Sum>v<Suc n. real (Poly_Mapping.lookup J v) / real (r n))"
    by (rule sum_mono) (use step in auto)
  also have "\<dots> = real (roth_total_order (Suc n) J) / real (r n)"
    by (simp add: roth_total_order_def sum_divide_distrib add_divide_distrib)
  finally show ?thesis .
qed

lemma roth_weight_extend_zero:
  assumes supp: "Poly_Mapping.keys J \<subseteq> {..<n}"
  shows "roth_weight (Suc n) r J = roth_weight n r J"
proof -
  have "Poly_Mapping.lookup J n = 0"
    using supp by (auto simp: in_keys_iff)
  then show ?thesis by (simp add: roth_weight_def)
qed

lemma roth_weight_tensor_bound:
  assumes supp: "Poly_Mapping.keys J \<subseteq> {..<Suc n}"
    and ord: "roth_total_order (Suc n) J \<le> i"
    and ib: "i \<le> r (Suc n)"
    and rp: "0 < r n"
    and rb: "\<And>v. v<n \<Longrightarrow> r n \<le> r v"
  shows "roth_weight (Suc (Suc n)) r (J + Poly_Mapping.single (Suc n) j) \<le>
    real (r (Suc n)) / real (r n) + real j / real (r (Suc n))"
proof -
  have ext: "roth_weight (Suc (Suc n)) r J = roth_weight (Suc n) r J"
    using roth_weight_extend_zero supp by blast
  have pref: "roth_weight (Suc n) r J \<le> real (roth_total_order (Suc n) J) / real (r n)"
    by (rule roth_weight_prefix_bound) (use supp rp rb in auto)
  have order_le: "real (roth_total_order (Suc n) J) / real (r n) \<le>
    real (r (Suc n)) / real (r n)"
    using ord ib rp by (intro divide_right_mono) auto
  then show ?thesis
    using roth_weight_add roth_weight_single ext pref by force
qed

lemma roth_halving_antitone:
  fixes r :: "nat \<Rightarrow> nat"
  assumes half: "\<And>v. Suc v < m \<Longrightarrow> 2 * r (Suc v) \<le> r v"
    and v: "u \<le> v" "v<m"
  shows "r v \<le> r u"
  using v
proof (induction v arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc v)
  then show ?case
    using half le_Suc_eq n_less_m_mult_n order_le_less by fastforce
qed

lemma roth_weight_tensor_halving:
  assumes half: "\<And>v. Suc v < Suc (Suc n) \<Longrightarrow>
      2 * r (Suc v) \<le> r v"
    and supp: "Poly_Mapping.keys J \<subseteq> {..<Suc n}"
    and ord: "roth_total_order (Suc n) J \<le> i"
    and ib: "i \<le> r (Suc n)"
    and rp: "0 < r n"
  shows "roth_weight (Suc (Suc n)) r (J + Poly_Mapping.single (Suc n) j) \<le>
         real (r (Suc n)) / real (r n) + real j / real (r (Suc n))"
proof (rule roth_weight_tensor_bound[OF supp ord ib rp])
  fix v assume vn: "v<n"
  with half show "r n \<le> r v"
    by (intro roth_halving_antitone [where r=r and m="Suc (Suc n)"]) auto
qed

lemma roth_index_det_hasse_weight:
  fixes P :: "rat mpoly"
  assumes ip: "roth_index m r a P = ereal t"
    and wb: "\<And>i j. i<k \<Longrightarrow> j<k \<Longrightarrow>
      roth_weight m r (J i j) \<le> rho + real j / real R"
  shows "ereal (\<Sum>j<k. max 0 (t-rho-real j / real R)) \<le>
         roth_index m r a (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P)))"
proof (rule roth_index_det_lower)
  fix q assume q: "q permutes {..<k}"
  have b: "ereal (max 0 (t-rho-real (q i) / R)) \<le> roth_index m r a (roth_hasse (J i (q i)) P)" 
    if ik: "i<k" for i
  proof -
    have w: "roth_weight m r (J i (q i)) \<le> rho + real (q i) / real R"
      by (simp add: q roth_permutes_bounded that wb) 
    with roth_index_hasse_lower[OF ip w]
    show ?thesis by (simp add: algebra_simps)
  qed
  show "ereal (\<Sum>j<k. max 0 (t-rho-real j / real R)) \<le>
        (\<Sum>i<k. roth_index m r a (roth_hasse (J i (q i)) P))"
    using roth_permutes_sum[OF q]
    by (metis (mono_tags, lifting) b lessThan_iff sum_ereal sum_mono)
qed

lemma roth_max_shift_sum:
  fixes rho t :: real
  assumes rn: "0 \<le> rho"
  shows "(\<Sum>j<k. max 0 (t-f j)) \<le> (\<Sum>j<k. max 0 (t-rho-f j)) + real k * rho"
proof -
  have step: "max 0 (t-f j) \<le> max 0 (t-rho-f j) + rho" for j
    using rn by (simp add: max_def; linarith)
  have "(\<Sum>j<k. max 0 (t-f j)) \<le> (\<Sum>j<k. max 0 (t-rho-f j) + rho)"
    by (rule sum_mono) (rule step)
  then show ?thesis by (simp add: sum.distrib)
qed

lemma roth_index_det_hasse_shift:
  fixes P :: "rat mpoly"
  assumes ip: "roth_index m r a P = ereal t"
    and wb: "\<And>i j. i<k \<Longrightarrow> j<k \<Longrightarrow> roth_weight m r (J i j) \<le> rho + j / R"
    and rn: "0 \<le> rho"
  defines "V \<equiv> det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))"
  defines "T \<equiv> (\<Sum>j<k. max 0 (t-real j / real R))"
  shows "ereal T \<le> roth_index m r a V + ereal (k * rho)"
proof -
  let ?S = "(\<Sum>j<k. max 0 (t-rho-real j / real R))"
  have h: "ereal ?S \<le> roth_index m r a V"
    unfolding V_def by (rule roth_index_det_hasse_weight[OF ip wb])
  have num: "T \<le> ?S + real k * rho"
    using T_def rn roth_max_shift_sum by presburger
  have "ereal T \<le> ereal ?S + ereal (real k * rho)"
    using num by simp
  also have "\<dots> \<le> roth_index m r a V + ereal (real k * rho)"
    by (rule add_right_mono[OF h])
  finally show ?thesis .
qed

theorem roth_tensor_det_index_lower:
  fixes P :: "rat mpoly"
  assumes ip: "roth_index (Suc (Suc n)) r a P = ereal t"
    and half: "\<And>v. Suc v < Suc (Suc n) \<Longrightarrow> 2 * r (Suc v) \<le> r v"
    and rp: "0 < r n"
    and rl: "0 < r(Suc n)"
    and kn: "k \<le> Suc (r (Suc n))"
    and row: "\<And>i. i<k \<Longrightarrow>
      Poly_Mapping.keys (mu i) \<subseteq> {..<Suc n} \<and> roth_total_order (Suc n) (mu i) \<le> i"
  shows "ereal (\<Sum>j<k. max 0 (t - real j / real (r (Suc n)))) \<le>
    roth_index (Suc (Suc n)) r a
      (det (mat k k (\<lambda>(i,j). roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P))) +
    ereal (real k * (r (Suc n) / (r n)))"
proof (rule roth_index_det_hasse_shift[OF ip])
  fix i j assume ik: "i<k" and jk: "j<k"
  have ib: "i \<le> r (Suc n)" using ik kn by arith
  show "roth_weight (Suc (Suc n)) r (mu i + Poly_Mapping.single (Suc n) j) \<le>
         r (Suc n) / (r n) + j / r (Suc n)"
    by (rule roth_weight_tensor_halving)
      (use half row[OF ik] ib rp in auto)
qed (use rp in auto)

section \<open>Quadratic finite-sum estimate\<close>

lemma roth_ceiling_cutoff:
  fixes t :: real and R::nat
  defines "n \<equiv> nat \<lceil>real R*t/2\<rceil>"
  assumes t0: "0\<le>t" and t1: "t\<le>1" and Rp: "0<R" and "j<n"
  shows "real j / real R < t/2"
proof -
  have "int j < \<lceil>real R*t/2\<rceil>"
    using \<open>j<n\<close> t0 unfolding n_def by simp
  then have "real j < real R*t/2"
    by (simp add: less_ceiling_iff)
  then show ?thesis
    using Rp by (simp add: field_simps divide_less_eq)
qed

lemma roth_sum_cutoff_lower:
  fixes t :: real
  assumes t0: "0\<le>t" and np: "0<n" and nk: "n\<le>k"
    and jb: "\<And>j. j<n \<Longrightarrow> real j / real R \<le> t/2"
  shows "real n*t/2 + t/2 \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
proof -
  let ?f = "\<lambda>j. max 0 (t-real j / real R)"
  let ?g = "\<lambda>j. t/2 + (if j=0 then t/2 else 0)"
  have step: "?g j \<le> ?f j" if jn: "j<n" for j
    using t0 jb[OF jn] that by (simp add: max_def; linarith)
  have "real n*t/2 + t/2 = (\<Sum>j<n. ?g j)"
    using np by (simp add: sum.distrib algebra_simps)
  also have "\<dots> \<le> (\<Sum>j<n. ?f j)"
    by (rule sum_mono) (use step in auto)
  also have "\<dots> \<le> (\<Sum>j<k. ?f j)"
    by (rule sum_mono2) (use nk in auto)
  finally show ?thesis .
qed

lemma roth_sum_quadratic_small:
  fixes t :: real
  assumes t0: "0\<le>t" and t1: "t\<le>1" and Rp: "0<R" and kR: "k\<le>Suc R"
  shows "real k * t^2 / 4 \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
proof (cases "k=0 \<or> t=0")
  case True
  then show ?thesis by auto
next
  case False
  then have kp: "0<k" and tp: "0<t" using t0 by auto
  let ?n = "nat \<lceil>real R*t/2\<rceil>"
  have jn: "\<And>j. j<?n \<Longrightarrow> real j / real R < t/2"
    using roth_ceiling_cutoff[OF t0 t1 Rp] by auto
  have nx: "real R*t/2 \<le> real ?n"
    by (rule of_nat_ceiling)
  have np: "0<?n" using nx tp Rp by auto
  have t2: "t^2 \<le> t"
    using mult_left_mono[OF t1, of t] t0
    by (simp add: power2_eq_square)
  show ?thesis
  proof (cases "k\<le>?n")
    case True
    have jb: "real j / real R \<le> t/2" if "j<k" for j
      using that jn True
      by (smt (verit, del_insts) order_less_le_trans)
    have low: "real k*t/2 + t/2 \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
      by (rule roth_sum_cutoff_lower[where n=k and R=R])
        (use t0 kp jb in auto)
    have tt: "t^2/4 \<le> t/2"
      using t0 t2 by auto
    have "real k * t^2 / 4 \<le> real k*t/2"
      using mult_left_mono[OF tt, of "real k"] by simp
    also have "real k*t/2 \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
      using t0 low by linarith
    finally show ?thesis .
  next
    case False
    then have nk: "?n\<le>k" by arith
    have low: "real ?n*t/2 + t/2 \<le> (\<Sum>j<k. max 0 (t-real j / R))"
      using t0 np nk jn
      by (intro roth_sum_cutoff_lower; fastforce)
    have a: "real R*t^2/4 \<le> real ?n*t/2"
      using mult_right_mono[OF nx] t0 by (simp add: power2_eq_square algebra_simps)
    have b: "real k*(t^2/4) \<le> (real R+1)*(t^2/4)"
      by (rule mult_right_mono) (use kR in auto)
    have tt: "t^2/4 \<le> t/2"
      using t0 t2 by simp
    have c: "(real R+1)*(t^2/4) \<le> real R*(t^2/4)+t/2"
      using add_left_mono[OF tt, of "real R*(t^2/4)"]
      by (simp add: algebra_simps)
    show ?thesis using low a b c by argo
  qed
qed

lemma roth_sum_nat_id: "(\<Sum>j<k. real j) = real k * real (k-1) / 2"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case
    by (cases "k=0") (auto simp: sum.lessThan_Suc algebra_simps)
qed

lemma roth_sum_large_half:
  fixes t :: real
  assumes t1: "1\<le>t" and Rp: "0<R" and kR: "k\<le>Suc R"
  shows "real k*t/2 \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
proof -
  have jr: "real j / real R \<le> 1" if jk: "j<k" for j
    using Rp kR that by auto
  have kl: "real (k-1) / real R \<le> 1"
    using Rp kR by auto
  have mid: "real k * real (k-1) / (2*real R) \<le> real k/2"
    using mult_left_mono[OF kl] by auto
  have nonneg: "0 \<le> t-real j / real R" if "j<k" for j
    using jr[OF that] t1 by linarith
  have eq: "(\<Sum>j<k. max 0 (t-real j / real R)) =
    (\<Sum>j<k. t-real j / real R)"
    by (rule sum.cong) (use nonneg in auto)
  have formula: "(\<Sum>j<k. max 0 (t-real j / real R)) = real k*t - real k * real (k-1) / (2*real R)"
    by (simp add: eq sum_subtractf sum_divide_distrib[symmetric]
      roth_sum_nat_id algebra_simps)
  have lower: "real k*t/2 \<le> real k*t-real k/2"
    using mult_left_mono[OF t1, of "real k/2"] by linarith
  with mid formula show ?thesis
    by linarith
qed

theorem roth_sum_quadratic:
  fixes t :: real
  assumes t0: "0\<le>t" and tm: "t\<le>real m"
    and m2: "2\<le>m" and Rp: "0<R" and kR: "k\<le>Suc R"
  shows "real k * t^2 / (2*real m) \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
proof (cases "t\<le>1")
  case True
  have small: "real k*t^2/4 \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
    by (rule roth_sum_quadratic_small[OF t0 True Rp kR])
  have td: "t^2/(2*real m) \<le> t^2/4"
    by (rule divide_left_mono) (use m2 in auto)
  have "real k*t^2/(2*real m) = real k*(t^2/(2*real m))"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> real k*(t^2/4)"
    by (rule mult_left_mono[OF td]) simp
  also have "\<dots> \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
    using small by linarith
  finally show ?thesis .
next
  case False
  then have t1: "1\<le>t" by simp
  have large: "real k*t/2 \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
    by (rule roth_sum_large_half[OF t1 Rp kR])
  have td: "t^2/(2*real m) \<le> t/2"
    using mult_right_mono[OF tm, of t] t0 m2 
    by (simp add: power2_eq_square field_simps)
  have "real k*t^2/(2*real m) = real k*(t^2/(2*real m))"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> real k*(t/2)"
    by (rule mult_left_mono[OF td]) simp
  also have "\<dots> \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
    using large by linarith
  finally show ?thesis .
qed

theorem roth_tensor_det_index_quadratic:
  fixes P :: "rat mpoly"
  assumes ip: "roth_index (Suc (Suc n)) r a P = ereal t"
    and t0: "0\<le>t" and tm: "t\<le>real (Suc (Suc n))"
    and half: "\<And>v. Suc v < Suc (Suc n) \<Longrightarrow>
      2 * r (Suc v) \<le> r v"
    and rp: "0<r n" and rl: "0<r (Suc n)"
    and kn: "k \<le> Suc (r (Suc n))"
    and row: "\<And>i. i<k \<Longrightarrow>
      Poly_Mapping.keys (mu i) \<subseteq> {..<Suc n} \<and>
      roth_total_order (Suc n) (mu i) \<le> i"
  shows "ereal (real k * t^2 / (2 * real (Suc (Suc n)))) \<le>
    roth_index (Suc (Suc n)) r a
      (det (mat k k (\<lambda>(i,j). roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P))) +
    ereal (real k * (real (r (Suc n)) / real (r n)))"
proof -
  have num: "real k * t^2 / (2 * real (Suc (Suc n))) \<le> (\<Sum>j<k. max 0 (t - real j / real (r (Suc n))))"
    by (rule roth_sum_quadratic[OF t0 tm _ rl kn]) simp
  with roth_tensor_det_index_lower[OF ip] 
  show ?thesis
    using ereal_le_le half kn rl row rp by blast
qed

section \<open>Index attained inside the degree box\<close>

lemma roth_box_weight_le_dim:
  assumes box: "I \<in> roth_exponent_box m r"
    and pos: "\<And>v. v<m \<Longrightarrow> 0 < r v"
  shows "roth_weight m r I \<le> real m"
proof -
  have step: "real (Poly_Mapping.lookup I v) / real (r v) \<le> 1"
    if vm: "v<m" for v
    using box pos roth_exponent_boxD(2) vm by force
  have "roth_weight m r I \<le> (\<Sum>v<m. (1::real))"
    unfolding roth_weight_def by (meson step lessThan_iff sum_mono)
  then show ?thesis by simp
qed

lemma roth_index_box_attained:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "P\<noteq>0"
    and pos: "\<And>v. v<m \<Longrightarrow> 0<r v"
  obtains t where "roth_index m r a P = ereal t" "0\<le>t" "t\<le>real m"
proof -
  obtain I where tc: "roth_taylor_coeff a I P \<noteq> 0"
    and ip: "roth_index m r a P = ereal (roth_weight m r I)"
    using roth_index_attained[OF nz] by blast
  have ibox: "I\<in>roth_exponent_box m r"
    by (rule roth_taylor_index_box[OF box tc])
  have w: "roth_weight m r I \<le> m"
    by (simp add: ibox pos roth_box_weight_le_dim)
  show thesis
    by (rule that[OF ip roth_weight_nonneg w])
qed

lemma roth_halving_positive_all:
  fixes r :: "nat \<Rightarrow> nat"
  assumes half: "\<And>v. Suc v < Suc (Suc n) \<Longrightarrow> 2 * r (Suc v) \<le> r v"
    and rp: "0<r n" and rl: "0<r (Suc n)"
    and vm: "v < Suc (Suc n)"
  shows "0<r v"
proof (cases "v = Suc n")
  case True
  then show ?thesis using rl by simp
next
  case False
  then have vn: "v\<le>n" using vm by arith
  with half have le: "r n \<le> r v"
    by (intro roth_halving_antitone [where r=r and m="Suc (Suc n)"]) auto
  show ?thesis using rp le by arith
qed

theorem roth_tensor_det_index_quadratic_box:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box (Suc (Suc n)) r P"
    and nz: "P\<noteq>0"
    and half: "\<And>v. Suc v < Suc (Suc n) \<Longrightarrow> 2 * r (Suc v) \<le> r v"
    and rp: "0<r n" and rl: "0<r (Suc n)"
    and kn: "k \<le> Suc (r (Suc n))"
    and row: "\<And>i. i<k \<Longrightarrow>
      Poly_Mapping.keys (mu i) \<subseteq> {..<Suc n} \<and>
      roth_total_order (Suc n) (mu i) \<le> i"
  shows "ereal (real k * (real_of_ereal (roth_index (Suc (Suc n)) r a P))^2 /
        (2 * real (Suc (Suc n)))) \<le>
    roth_index (Suc (Suc n)) r a
      (det (mat k k (\<lambda>(i,j). roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P))) +
    ereal (real k * (real (r (Suc n)) / real (r n)))"
proof -
  have pos: "0<r v" if "v<Suc (Suc n)" for v
    by (rule roth_halving_positive_all)
      (use half rp rl that in auto)
  obtain t where ip: "roth_index (Suc (Suc n)) r a P = ereal t"
    and t0: "0\<le>t" and tm: "t\<le>real (Suc (Suc n))"
    by (rule roth_index_box_attained[OF box nz]) (use pos in auto)
  have q: "ereal (real k * t^2 / (2 * real (Suc (Suc n)))) \<le>
    roth_index (Suc (Suc n)) r a
      (det (mat k k (\<lambda>(i,j).
        roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P))) +
    ereal (real k *
      (real (r (Suc n)) / real (r n)))"
    by (rule roth_tensor_det_index_quadratic[OF ip t0 tm])
      (use half rp rl kn row in auto)
  show ?thesis using q by (simp add: ip)
qed

section \<open>Nonzero factors of the tensor determinant\<close>

text \<open>A tensor determinant witness records the separated nonzero factors,
  together with the admissible derivative rows that produce their product.\<close>

definition roth_tensor_det_witness where
  "roth_tensor_det_witness n k P mu U L \<equiv>
    (\<forall>i<k. Poly_Mapping.keys (mu i) \<subseteq> {..<n} \<and>
      roth_total_order n (mu i) \<le> i) \<and> U \<noteq> 0 \<and> L \<noteq> 0 \<and>
    det (mat k k (\<lambda>(i,j). roth_hasse (mu i + Poly_Mapping.single n j) P)) = U * L"

theorem roth_tensor_det_factors:
  fixes phi psi :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>l<k. roth_poly_in_box n r (phi l)"
    and li: "roth_mpoly_indep k phi"
    and qv: "\<And>l. l<k \<Longrightarrow> vars (psi l) \<subseteq> {n}"
    and ri: "roth_poly_indep k (\<lambda>l. mpoly_to_poly n (psi l))"
  shows "\<exists>mu U L.
    roth_tensor_det_witness n k (\<Sum>l<k. phi l * psi l) mu U L \<and>
    U = det (mat k k (\<lambda>(i,l). roth_hasse (mu i) (phi l))) \<and>
    L = det (mat k k (\<lambda>(l,j). roth_hasse (Poly_Mapping.single n j) (psi l)))"
proof -
  obtain mu where row: "\<forall>i<k.
      Poly_Mapping.keys (mu i) \<subseteq> {..<n} \<and>
      roth_total_order n (mu i) \<le> i"
    and un: "det (mat k k (\<lambda>(i,l).
      roth_hasse (mu i) (phi l))) \<noteq> 0"
    using roth_generalized_wronskian[OF box li] by blast
  have ln: "det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (psi l))) \<noteq> 0"
    by (rule roth_right_det_nonzero[OF qv ri])
  have pv: "\<And>l. l<k \<Longrightarrow> vars (phi l) \<subseteq> {..<n}"
    by (rule roth_tensor_box_vars[OF box])
  show ?thesis unfolding roth_tensor_det_witness_def
  proof (intro exI strip conjI)
    show "det (mat k k (\<lambda>(i,j). roth_hasse (mu i + Poly_Mapping.single n j)
                                (\<Sum>l<k. phi l * psi l))) =
         det (mat k k (\<lambda>(i,l). roth_hasse (mu i) (phi l))) *
         det (mat k k (\<lambda>(l,j). roth_hasse (Poly_Mapping.single n j) (psi l)))"
      by (rule roth_tensor_det_factorization) (use row pv qv in auto)
  qed (use ln un row in auto)
qed


lemma roth_vars_uminus_rat:
  "vars (-(P::rat mpoly)) = vars P"
  by (simp add: vars_def uminus_mpoly.rep_eq)

lemma roth_vars_sign_mult:
  "vars (signof q * (P::rat mpoly)) = vars P"
  by (simp add: sign_def roth_vars_uminus_rat)

lemma roth_det_vars_subset:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
  assumes ab: "\<And>i j. i<k \<Longrightarrow> j<k \<Longrightarrow> vars (A i j) \<subseteq> S"
  shows "vars (det (mat k k (\<lambda>(i,j). A i j))) \<subseteq> S"
proof -
  let ?Q = "{q. q permutes {..<k}}"
  have tvar: "vars (signof q * (\<Prod>i<k. A i (q i))) \<subseteq> S"
    if q: "q\<in>?Q" for q
  proof -
    have v: "vars (\<Prod>i<k. A i (q i)) \<subseteq> (\<Union>i<k. vars (A i (q i)))"
      by (rule roth_vars_prod_subset) simp
    have uv: "(\<Union>i<k. vars (A i (q i))) \<subseteq> S"
      using ab roth_permutes_bounded q by blast
    show ?thesis using v uv by (simp add: roth_vars_sign_mult)
  qed
  have v: "vars (\<Sum>q\<in>?Q. signof q * (\<Prod>i<k. A i (q i)))
    \<subseteq> (\<Union>q\<in>?Q. vars (signof q * (\<Prod>i<k. A i (q i))))"
    by (rule vars_setsum) (simp add: finite_permutations)
  show ?thesis using v tvar
    by (auto simp: roth_det_mat_expansion)
qed


lemma roth_det_left_vars:
  fixes phi :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>l<k. roth_poly_in_box n r (phi l)"
  shows "vars (det (mat k k (\<lambda>(i,l). roth_hasse (mu i) (phi l)))) \<subseteq> {..<n}"
  using box
  by (meson order_trans roth_box_vars roth_det_vars_subset roth_hasse_vars_subset)

lemma roth_det_right_vars:
  fixes psi :: "nat \<Rightarrow> rat mpoly"
  assumes qv: "\<And>l. l<k \<Longrightarrow> vars (psi l) \<subseteq> {n}"
  shows "vars (det (mat k k (\<lambda>(l,j).
      roth_hasse (Poly_Mapping.single n j) (psi l)))) \<subseteq> {n}"
  using qv roth_hasse_vars_subset by (intro roth_det_vars_subset) blast

lemma roth_det_left_box:
  fixes phi :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>l<k. roth_poly_in_box n r (phi l)"
  shows "roth_poly_in_box n (\<lambda>v. k*r v)
    (det (mat k k (\<lambda>(i,l). roth_hasse (mu i) (phi l))))"
  using box roth_box_det roth_hasse_preserves_box by presburger

lemma roth_det_right_box:
  fixes psi :: "nat \<Rightarrow> rat mpoly"
  assumes box: "\<forall>l<k. roth_poly_in_box (Suc n) r (psi l)"
  shows "roth_poly_in_box (Suc n) (\<lambda>v. k*r v) (det (mat k k (\<lambda>(l,j).
                 roth_hasse (Poly_Mapping.single n j) (psi l))))"
  using box roth_box_det roth_hasse_preserves_box by presburger


theorem roth_box_tensor_det_factors_bounded:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box (Suc n) r P"
    and nz: "P \<noteq> 0"
  shows "\<exists>k mu U L.
    0 < k \<and> k \<le> Suc (r n) \<and>
    roth_tensor_det_witness n k P mu U L \<and>
    roth_poly_in_box n (\<lambda>v. k*r v) U \<and>
    roth_poly_in_box (Suc n) (\<lambda>v. k*r v) L \<and>
    vars U \<subseteq> {..<n} \<and> vars L \<subseteq> {n}"
proof -
  obtain B where sub: "B \<subseteq> roth_last_coeff P n ` {..r n}"
    and ne: "B \<noteq> {}" and bd: "card B \<le> Suc (r n)"
    and ind: "roth_vs.independent B"
    and boxB: "\<forall>b\<in>B. roth_poly_in_box n r b"
    and spl: "P = (\<Sum>b\<in>B.
      b * roth_right_factor P n (r n) B b)"
    using roth_tensor_basis_exists[OF box nz]
    unfolding roth_tensor_basis_def by blast
  have fin: "finite B" 
    by (meson sub finite_subset finite_imageI finite_atMost)
  let ?k = "card B"
  let ?phi = "from_nat_into B"
  let ?psi = "\<lambda>l. roth_right_factor P n (r n) B (?phi l)"
  have bij: "bij_betw ?phi {..<?k} B"
    by (rule Countable_Set.bij_betw_from_nat_into_finite[OF fin])
  have boxphi: "\<forall>l<?k. roth_poly_in_box n r (?phi l)"
    using bij boxB by (auto simp: bij_betw_def)
  have li: "roth_mpoly_indep ?k ?phi"
    by (rule roth_indexed_set_indep[OF bij ind])
  have qv: "\<And>l. l<?k \<Longrightarrow> vars (?psi l) \<subseteq> {n}"
    by (rule roth_right_factor_vars)
  have ri: "roth_poly_indep ?k (\<lambda>l. mpoly_to_poly n (?psi l))"
    by (rule roth_indexed_right_indep[OF bij sub ind fin])
  have peq: "P = (\<Sum>l<?k. ?phi l * ?psi l)"
    by (rule roth_indexed_tensor_split[OF bij spl])
  obtain mu U L where
        wit: "roth_tensor_det_witness n ?k (\<Sum>l<?k. ?phi l * ?psi l) mu U L"
    and ue: "U = det (mat ?k ?k (\<lambda>(i,l). roth_hasse (mu i) (?phi l)))"
    and le: "L = det (mat ?k ?k (\<lambda>(l,j). roth_hasse (Poly_Mapping.single n j) (?psi l)))"
    using roth_tensor_det_factors[OF boxphi li qv ri] by blast
  have kp: "0<?k" using ne fin by (simp add: card_gt_0_iff)
  have boxpsi: "\<forall>l<?k. roth_poly_in_box (Suc n) r (?psi l)"
    by (simp add: roth_right_factor_box)
  have witP: "roth_tensor_det_witness n ?k P mu U L"
    using wit peq by simp
  have ub: "roth_poly_in_box n (\<lambda>v. ?k*r v) U"
    unfolding ue by (rule roth_det_left_box[OF boxphi])
  have lb: "roth_poly_in_box (Suc n) (\<lambda>v. ?k*r v) L"
    unfolding le by (rule roth_det_right_box[OF boxpsi])
  have uv: "vars U \<subseteq> {..<n}"
    unfolding ue by (rule roth_det_left_vars[OF boxphi])
  have lv: "vars L \<subseteq> {n}"
    unfolding le by (rule roth_det_right_vars[OF qv])
  show ?thesis using kp bd witP ub lb uv lv
    by blast
qed

end
