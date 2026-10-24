theory Roth_Determinant_Index
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
  have x: "theta \<le> roth_index m r a (F x)"
    using insert.prems by simp
  have s: "theta \<le> roth_index m r a (\<Sum>x\<in>S. F x)"
    using insert.IH insert.prems by auto
  have "theta \<le> min (roth_index m r a (F x))
      (roth_index m r a (\<Sum>x\<in>S. F x))"
    using x s by simp
  also have "... \<le> roth_index m r a (\<Sum>x\<in>insert x S. F x)"
    using insert.hyps by (simp add: roth_index_add)
  finally show ?case .
qed

lemma roth_index_prod_lower:
  fixes F :: "'b \<Rightarrow> rat mpoly"
  assumes fin: "finite S"
  shows "(\<Sum>x\<in>S. roth_index m r a (F x)) \<le>
    roth_index m r a (\<Prod>x\<in>S. F x)"
  using fin
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: roth_index_nonneg)
next
  case (insert x S)
  have "roth_index m r a (F x) +
    (\<Sum>y\<in>S. roth_index m r a (F y)) \<le>
    roth_index m r a (F x) +
      roth_index m r a (\<Prod>y\<in>S. F y)"
    by (rule add_left_mono[OF insert.IH])
  also have "... \<le>
    roth_index m r a (F x * (\<Prod>y\<in>S. F y))"
    by (rule roth_index_mult)
  finally show ?case using insert.hyps by simp
qed

lemma roth_index_left_mult_lower:
  fixes P Q :: "rat mpoly"
  shows "roth_index m r a Q \<le> roth_index m r a (P*Q)"
proof -
  have "roth_index m r a Q \<le>
    roth_index m r a P + roth_index m r a Q"
    using add_right_mono[OF roth_index_nonneg[of m r a P],
      of "roth_index m r a Q"] by simp
  also have "... \<le> roth_index m r a (P*Q)"
    by (rule roth_index_mult)
  finally show ?thesis .
qed

lemma roth_index_det_lower:
  fixes A :: "nat \<Rightarrow> nat \<Rightarrow> rat mpoly"
  assumes bd: "\<And>q. q permutes {..<k} \<Longrightarrow>
    theta \<le> (\<Sum>i<k. roth_index m r a (A i (q i)))"
  shows "theta \<le> roth_index m r a
    (det (mat k k (\<lambda>(i,j). A i j)))"
proof -
  let ?Q = "{q. q permutes {..<k}}"
  have fin: "finite ?Q" by (rule finite_permutations) simp
  have each: "theta \<le> roth_index m r a
      (signof q * (\<Prod>i<k. A i (q i)))" if q: "q\<in>?Q" for q
  proof -
    have "theta \<le> (\<Sum>i<k. roth_index m r a (A i (q i)))"
      by (rule bd) (use q in auto)
    also have "... \<le>
      roth_index m r a (\<Prod>i<k. A i (q i))"
      by (rule roth_index_prod_lower) simp
    also have "... \<le> roth_index m r a
      (signof q * (\<Prod>i<k. A i (q i)))"
      by (rule roth_index_left_mult_lower)
    finally show ?thesis .
  qed
  show ?thesis unfolding roth_det_mat_expansion
    by (rule roth_index_sum_lower[OF fin]) (rule each)
qed

lemma roth_index_hasse_lower:
  fixes P :: "rat mpoly"
  assumes ip: "roth_index m r a P = ereal t"
    and w: "roth_weight m r J \<le> L"
  shows "ereal (max 0 (t-L)) \<le>
    roth_index m r a (roth_hasse J P)"
proof -
  have h: "ereal (t - roth_weight m r J) \<le>
    roth_index m r a (roth_hasse J P)"
    using roth_index_hasse[of m r a P J] ip by simp
  have le: "t-L \<le> t - roth_weight m r J"
    using w by simp
  have hl: "ereal (t-L) \<le> roth_index m r a (roth_hasse J P)"
  proof -
    have "ereal (t-L) \<le> ereal (t - roth_weight m r J)"
      using le by simp
    then show ?thesis using h by (rule order_trans)
  qed
  show ?thesis using hl roth_index_nonneg[of m r a "roth_hasse J P"]
    by (simp add: zero_ereal_def)
qed

lemma roth_weight_single:
  assumes vm: "v<m"
  shows "roth_weight m r (Poly_Mapping.single v j) =
    real j / real (r v)"
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
  shows "roth_weight (Suc n) r J \<le>
    real (roth_total_order (Suc n) J) / real (r n)"
proof -
  have step: "real (Poly_Mapping.lookup J v) / real (r v) \<le>
    real (Poly_Mapping.lookup J v) / real (r n)"
    if vn: "v<Suc n" for v
  proof (cases "v=n")
    case True
    then show ?thesis by simp
  next
    case False
    have vn': "v<n" using vn False by arith
    show ?thesis by (rule divide_left_mono)
      (use rp rb[OF vn'] in auto)
  qed
  have "roth_weight (Suc n) r J =
    (\<Sum>v<Suc n. real (Poly_Mapping.lookup J v) / real (r v))"
    by (simp add: roth_weight_def)
  also have "... \<le>
    (\<Sum>v<Suc n. real (Poly_Mapping.lookup J v) / real (r n))"
    by (rule sum_mono) (use step in auto)
  also have "... = real (roth_total_order (Suc n) J) / real (r n)"
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
  shows "roth_weight (Suc (Suc n)) r
    (J + Poly_Mapping.single (Suc n) j) \<le>
    real (r (Suc n)) / real (r n) +
      real j / real (r (Suc n))"
proof -
  have ext: "roth_weight (Suc (Suc n)) r J =
    roth_weight (Suc n) r J"
    by (rule roth_weight_extend_zero)
      (use supp in auto)
  have pref: "roth_weight (Suc n) r J \<le>
    real (roth_total_order (Suc n) J) / real (r n)"
    by (rule roth_weight_prefix_bound) (use supp rp rb in auto)
  have order_le: "real (roth_total_order (Suc n) J) / real (r n) \<le>
    real (r (Suc n)) / real (r n)"
    using ord ib rp by (intro divide_right_mono) auto
  have "roth_weight (Suc (Suc n)) r
    (J + Poly_Mapping.single (Suc n) j) =
    roth_weight (Suc (Suc n)) r J +
      real j / real (r (Suc n))"
    by (simp add: roth_weight_add roth_weight_single)
  also have "... \<le>
    real (r (Suc n)) / real (r n) +
      real j / real (r (Suc n))"
    using pref order_le by (simp add: ext)
  finally show ?thesis .
qed

lemma roth_halving_antitone:
  fixes r :: "nat \<Rightarrow> nat"
  assumes half: "\<And>v. Suc v < m \<Longrightarrow> 2 * r (Suc v) \<le> r v"
    and uv: "u \<le> v" and vm: "v<m"
  shows "r v \<le> r u"
  using uv vm
proof (induction v arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc v)
  show ?case
  proof (cases "u = Suc v")
    case True
    then show ?thesis by simp
  next
    case False
    have uv: "u\<le>v" using Suc.prems False by arith
    have vm: "v<m" using Suc.prems by arith
    have h: "2 * r (Suc v) \<le> r v" by (rule half[OF Suc.prems(2)])
    have ih: "r v \<le> r u" by (rule Suc.IH[OF uv vm])
    show ?thesis using h ih by arith
  qed
qed

lemma roth_weight_tensor_halving:
  assumes half: "\<And>v. Suc v < Suc (Suc n) \<Longrightarrow>
      2 * r (Suc v) \<le> r v"
    and supp: "Poly_Mapping.keys J \<subseteq> {..<Suc n}"
    and ord: "roth_total_order (Suc n) J \<le> i"
    and ib: "i \<le> r (Suc n)"
    and rp: "0 < r n"
  shows "roth_weight (Suc (Suc n)) r
    (J + Poly_Mapping.single (Suc n) j) \<le>
    real (r (Suc n)) / real (r n) +
      real j / real (r (Suc n))"
proof (rule roth_weight_tensor_bound[OF supp ord ib rp])
  fix v assume vn: "v<n"
  show "r n \<le> r v"
    by (rule roth_halving_antitone
      [where r=r and m="Suc (Suc n)" and u=v and v=n])
      (use half vn in auto)
qed

lemma roth_permutes_sum_real:
  assumes q: "q permutes {..<k}"
  shows "(\<Sum>i<k. f (q i)::real) = (\<Sum>i<k. f i)"
proof -
  have inj: "inj_on q {..<k}"
    using q permutes_inj by (blast intro: inj_on_subset)
  have img: "q ` {..<k} = {..<k}"
    using permutes_image[OF q] .
  show ?thesis using sum.reindex[OF inj, of f] img
    by (simp add: o_def)
qed

lemma roth_index_det_hasse_weight:
  fixes P :: "rat mpoly"
  assumes ip: "roth_index m r a P = ereal t"
    and wb: "\<And>i j. i<k \<Longrightarrow> j<k \<Longrightarrow>
      roth_weight m r (J i j) \<le> rho + real j / real R"
  shows "ereal (\<Sum>j<k. max 0 (t-rho-real j / real R)) \<le>
    roth_index m r a
      (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P)))"
proof (rule roth_index_det_lower)
  fix q assume q: "q permutes {..<k}"
  have b: "ereal (max 0 (t-rho-real (q i) / real R)) \<le>
    roth_index m r a (roth_hasse (J i (q i)) P)" if ik: "i<k" for i
  proof -
    have qik: "q i<k" by (rule roth_permutes_bounded[OF q ik])
    have w: "roth_weight m r (J i (q i)) \<le>
      rho + real (q i) / real R" by (rule wb[OF ik qik])
    have h: "ereal (max 0 (t - (rho + real (q i) / real R))) \<le>
      roth_index m r a (roth_hasse (J i (q i)) P)"
      by (rule roth_index_hasse_lower[OF ip w])
    show ?thesis using h by (simp add: algebra_simps)
  qed
  have e: "(\<Sum>i<k. max 0 (t-rho-real (q i) / real R)) =
    (\<Sum>j<k. max 0 (t-rho-real j / real R))"
    by (rule roth_permutes_sum_real[OF q])
  show "ereal (\<Sum>j<k. max 0 (t-rho-real j / real R)) \<le>
    (\<Sum>i<k. roth_index m r a (roth_hasse (J i (q i)) P))"
    unfolding e[symmetric] sum_ereal[symmetric]
    by (rule sum_mono) (use b in auto)
qed

lemma roth_max_shift_sum:
  fixes rho t :: real
  assumes rn: "0 \<le> rho"
  shows "(\<Sum>j<k. max 0 (t-f j)) \<le>
    (\<Sum>j<k. max 0 (t-rho-f j)) + real k * rho"
proof -
  have step: "max 0 (t-f j) \<le>
    max 0 (t-rho-f j) + rho" for j
    using rn by (simp add: max_def; linarith)
  have "(\<Sum>j<k. max 0 (t-f j)) \<le>
    (\<Sum>j<k. max 0 (t-rho-f j) + rho)"
    by (rule sum_mono) (rule step)
  then show ?thesis by (simp add: sum.distrib)
qed

lemma roth_index_det_hasse_shift:
  fixes P :: "rat mpoly"
  assumes ip: "roth_index m r a P = ereal t"
    and wb: "\<And>i j. i<k \<Longrightarrow> j<k \<Longrightarrow>
      roth_weight m r (J i j) \<le> rho + real j / real R"
    and rn: "0 \<le> rho"
  shows "ereal (\<Sum>j<k. max 0 (t-real j / real R)) \<le>
    roth_index m r a
      (det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))) +
      ereal (real k * rho)"
proof -
  let ?V = "det (mat k k (\<lambda>(i,j). roth_hasse (J i j) P))"
  let ?S = "(\<Sum>j<k. max 0 (t-rho-real j / real R))"
  have h: "ereal ?S \<le> roth_index m r a ?V"
    by (rule roth_index_det_hasse_weight[OF ip wb])
  have num: "(\<Sum>j<k. max 0 (t-real j / real R)) \<le>
    ?S + real k * rho"
    by (rule roth_max_shift_sum[OF rn])
  have "ereal (\<Sum>j<k. max 0 (t-real j / real R)) \<le>
    ereal ?S + ereal (real k * rho)"
    using num by simp
  also have "... \<le> roth_index m r a ?V + ereal (real k * rho)"
    by (rule add_right_mono[OF h])
  finally show ?thesis .
qed

theorem roth_tensor_det_index_lower:
  fixes P :: "rat mpoly"
  assumes ip: "roth_index (Suc (Suc n)) r a P = ereal t"
    and half: "\<And>v. Suc v < Suc (Suc n) \<Longrightarrow>
      2 * r (Suc v) \<le> r v"
    and rp: "0<r n"
    and rl: "0<r (Suc n)"
    and kn: "k \<le> Suc (r (Suc n))"
    and row: "\<And>i. i<k \<Longrightarrow>
      Poly_Mapping.keys (mu i) \<subseteq> {..<Suc n} \<and>
      roth_total_order (Suc n) (mu i) \<le> i"
  shows "ereal (\<Sum>j<k. max 0
      (t - real j / real (r (Suc n)))) \<le>
    roth_index (Suc (Suc n)) r a
      (det (mat k k (\<lambda>(i,j).
        roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P))) +
    ereal (real k *
      (real (r (Suc n)) / real (r n)))"
proof (rule roth_index_det_hasse_shift[OF ip])
  fix i j assume ik: "i<k" and jk: "j<k"
  have ib: "i \<le> r (Suc n)" using ik kn by arith
  show "roth_weight (Suc (Suc n)) r
    (mu i + Poly_Mapping.single (Suc n) j) \<le>
    real (r (Suc n)) / real (r n) +
      real j / real (r (Suc n))"
    by (rule roth_weight_tensor_halving)
      (use half row[OF ik] ib rp in auto)
next
  show "0 \<le> real (r (Suc n)) / real (r n)"
    using rp by simp
qed

section \<open>Quadratic finite-sum estimate\<close>

lemma roth_ceiling_cutoff:
  fixes t :: real
  assumes t0: "0\<le>t" and t1: "t\<le>1" and Rp: "0<R"
  defines "n \<equiv> nat \<lceil>real R*t/2\<rceil>"
  shows "n\<le>R" "real R*t/2 \<le> real n"
    "\<And>j. j<n \<Longrightarrow> real j / real R < t/2"
proof -
  have x0: "0 \<le> real R*t/2" using t0 by simp
  have rt: "real R*t \<le> real R"
    using mult_left_mono[OF t1, of "real R"] by simp
  have xR: "real R*t/2 \<le> real R" using rt by linarith
  show "n\<le>R" unfolding n_def
    using x0 xR by (simp add: ceiling_le_iff)
  show "real R*t/2 \<le> real n" unfolding n_def
    by (rule of_nat_ceiling)
  fix j assume jn: "j<n"
  have jceil: "int j < \<lceil>real R*t/2\<rceil>"
    using jn x0 unfolding n_def by simp
  have "real j < real R*t/2"
    using jceil by (simp add: less_ceiling_iff)
  then have "real j < (t/2)*real R"
    by (simp add: field_simps)
  then show "real j / real R < t/2"
    using Rp by (simp add: divide_less_eq)
qed

lemma roth_sum_cutoff_lower:
  fixes t :: real
  assumes t0: "0\<le>t" and np: "0<n" and nk: "n\<le>k"
    and jb: "\<And>j. j<n \<Longrightarrow> real j / real R \<le> t/2"
  shows "real n*t/2 + t/2 \<le>
    (\<Sum>j<k. max 0 (t-real j / real R))"
proof -
  let ?f = "\<lambda>j. max 0 (t-real j / real R)"
  let ?g = "\<lambda>j. t/2 + (if j=0 then t/2 else 0)"
  have step: "?g j \<le> ?f j" if jn: "j<n" for j
  proof (cases "j=0")
    case True
    then show ?thesis using t0 by simp
  next
    case False
    then show ?thesis using t0 jb[OF jn]
      by (simp add: max_def; linarith)
  qed
  have "real n*t/2 + t/2 = (\<Sum>j<n. ?g j)"
    using np by (simp add: sum.distrib algebra_simps)
  also have "... \<le> (\<Sum>j<n. ?f j)"
    by (rule sum_mono) (use step in auto)
  also have "... \<le> (\<Sum>j<k. ?f j)"
    by (rule sum_mono2) (use nk in auto)
  finally show ?thesis .
qed

lemma roth_sum_quadratic_small:
  fixes t :: real
  assumes t0: "0\<le>t" and t1: "t\<le>1"
    and Rp: "0<R" and kR: "k\<le>Suc R"
  shows "real k * t^2 / 4 \<le>
    (\<Sum>j<k. max 0 (t-real j / real R))"
proof (cases "k=0 \<or> t=0")
  case True
  then show ?thesis by auto
next
  case False
  then have kp: "0<k" and tp: "0<t" using t0 by auto
  let ?n = "nat \<lceil>real R*t/2\<rceil>"
  have nR: "?n\<le>R" and nx: "real R*t/2 \<le> real ?n"
    and jn: "\<And>j. j<?n \<Longrightarrow> real j / real R < t/2"
    using roth_ceiling_cutoff[OF t0 t1 Rp] by auto
  have np: "0<?n" using nx tp Rp by auto
  have t2: "t^2 \<le> t"
    using mult_left_mono[OF t1, of t] t0
    by (simp add: power2_eq_square)
  show ?thesis
  proof (cases "k\<le>?n")
    case True
    have jb: "real j / real R \<le> t/2" if "j<k" for j
    proof -
      have "j<?n" using that True by arith
      then have "real j / real R < t/2" by (rule jn)
      then show ?thesis by (rule less_imp_le)
    qed
    have low: "real k*t/2 + t/2 \<le>
      (\<Sum>j<k. max 0 (t-real j / real R))"
      by (rule roth_sum_cutoff_lower[where n=k and R=R])
        (use t0 kp jb in auto)
    have tt: "t^2/4 \<le> t/2"
    proof -
      have "t^2/4 \<le> t/4" using t2 by (rule divide_right_mono) simp
      also have "t/4 \<le> t/2" using t0 by simp
      finally show ?thesis .
    qed
    have "real k * t^2 / 4 \<le> real k*t/2"
      using mult_left_mono[OF tt, of "real k"] by simp
    also have "real k*t/2 \<le> real k*t/2 + t/2" using t0 by simp
    also have "... \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
      by (rule low)
    finally show ?thesis .
  next
    case False
    then have nk: "?n\<le>k" by arith
    have jb: "real j / real R \<le> t/2" if "j<?n" for j
      using jn[OF that] by (rule less_imp_le)
    have low: "real ?n*t/2 + t/2 \<le>
      (\<Sum>j<k. max 0 (t-real j / real R))"
      by (rule roth_sum_cutoff_lower[where n="?n" and R=R])
        (use t0 np nk jb in auto)
    have mul: "(real R*t/2)*(t/2) \<le> real ?n*(t/2)"
      by (rule mult_right_mono[OF nx]) (use t0 in auto)
    have a: "real R*t^2/4 \<le> real ?n*t/2"
      using mul by (simp add: power2_eq_square algebra_simps)
    have b: "real k*(t^2/4) \<le> (real R+1)*(t^2/4)"
      by (rule mult_right_mono) (use kR in auto)
    have tt: "t^2/4 \<le> t/2"
    proof -
      have "t^2/4 \<le> t/4" using t2 by (rule divide_right_mono) simp
      also have "t/4 \<le> t/2" using t0 by simp
      finally show ?thesis .
    qed
    have c: "(real R+1)*(t^2/4) \<le> real R*(t^2/4)+t/2"
      using add_left_mono[OF tt, of "real R*(t^2/4)"]
      by (simp add: algebra_simps)
    show ?thesis using low a b c
      by (simp add: algebra_simps; linarith)
  qed
qed

lemma roth_sum_nat_id:
  "(\<Sum>j<k. real j) = real k * real (k-1) / 2"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases "k=0")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using Suc.IH
      by (simp add: sum.lessThan_Suc algebra_simps)
  qed
qed

lemma roth_sum_large_half:
  fixes t :: real
  assumes t1: "1\<le>t" and Rp: "0<R" and kR: "k\<le>Suc R"
  shows "real k*t/2 \<le>
    (\<Sum>j<k. max 0 (t-real j / real R))"
proof -
  have jr: "real j / real R \<le> 1" if jk: "j<k" for j
  proof -
    have "j\<le>R" using jk kR by arith
    then show ?thesis using Rp by (simp add: divide_le_eq)
  qed
  have nonneg: "0 \<le> t-real j / real R" if "j<k" for j
    using jr[OF that] t1 by linarith
  have eq: "(\<Sum>j<k. max 0 (t-real j / real R)) =
    (\<Sum>j<k. t-real j / real R)"
    by (rule sum.cong) (use nonneg in auto)
  have kl: "real (k-1) / real R \<le> 1"
  proof -
    have "k-1\<le>R" using kR by arith
    then show ?thesis using Rp by (simp add: divide_le_eq)
  qed
  have mid: "real k * real (k-1) / (2*real R) \<le> real k/2"
  proof -
    have "real k/2 * (real (k-1)/real R) \<le> real k/2 * 1"
      by (rule mult_left_mono[OF kl]) simp
    then show ?thesis by (simp add: algebra_simps)
  qed
  have formula: "(\<Sum>j<k. max 0 (t-real j / real R)) =
    real k*t - real k * real (k-1) / (2*real R)"
    by (simp add: eq sum_subtractf sum_divide_distrib[symmetric]
      roth_sum_nat_id algebra_simps)
  have khalf: "real k/2 \<le> real k*t/2"
    using mult_left_mono[OF t1, of "real k/2"]
    by (simp add: algebra_simps)
  have lower: "real k*t/2 \<le> real k*t-real k/2"
    using khalf by linarith
  have "real k*t/2 \<le> real k*t-real k/2"
    by (rule lower)
  also have "... \<le> real k*t - real k * real (k-1) / (2*real R)"
    using mid by simp
  also have "... = (\<Sum>j<k. max 0 (t-real j / real R))"
    using formula by simp
  finally show ?thesis .
qed

theorem roth_sum_quadratic:
  fixes t :: real
  assumes t0: "0\<le>t" and tm: "t\<le>real m"
    and m2: "2\<le>m" and Rp: "0<R" and kR: "k\<le>Suc R"
  shows "real k * t^2 / (2*real m) \<le>
    (\<Sum>j<k. max 0 (t-real j / real R))"
proof (cases "t\<le>1")
  case True
  have small: "real k*t^2/4 \<le>
    (\<Sum>j<k. max 0 (t-real j / real R))"
    by (rule roth_sum_quadratic_small[OF t0 True Rp kR])
  have td: "t^2/(2*real m) \<le> t^2/4"
    by (rule divide_left_mono) (use m2 in auto)
  have "real k*t^2/(2*real m) = real k*(t^2/(2*real m))"
    by (simp add: algebra_simps)
  also have "... \<le> real k*(t^2/4)"
    by (rule mult_left_mono[OF td]) simp
  also have "... = real k*t^2/4" by (simp add: algebra_simps)
  also have "... \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
    by (rule small)
  finally show ?thesis .
next
  case False
  then have t1: "1\<le>t" by simp
  have large: "real k*t/2 \<le>
    (\<Sum>j<k. max 0 (t-real j / real R))"
    by (rule roth_sum_large_half[OF t1 Rp kR])
  have sq: "t^2 \<le> real m*t"
    using mult_right_mono[OF tm, of t] t0
    by (simp add: power2_eq_square)
  have td: "t^2/(2*real m) \<le> t/2"
  proof -
    have "t^2/(2*real m) \<le> (real m*t)/(2*real m)"
      by (rule divide_right_mono[OF sq]) (use m2 in auto)
    then show ?thesis using m2 by simp
  qed
  have "real k*t^2/(2*real m) = real k*(t^2/(2*real m))"
    by (simp add: algebra_simps)
  also have "... \<le> real k*(t/2)"
    by (rule mult_left_mono[OF td]) simp
  also have "... = real k*t/2" by (simp add: algebra_simps)
  also have "... \<le> (\<Sum>j<k. max 0 (t-real j / real R))"
    by (rule large)
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
      (det (mat k k (\<lambda>(i,j).
        roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P))) +
    ereal (real k *
      (real (r (Suc n)) / real (r n)))"
proof -
  have num: "real k * t^2 / (2 * real (Suc (Suc n))) \<le>
    (\<Sum>j<k. max 0 (t - real j / real (r (Suc n))))"
    by (rule roth_sum_quadratic[OF t0 tm _ rl kn]) simp
  have det: "ereal (\<Sum>j<k. max 0
      (t - real j / real (r (Suc n)))) \<le>
    roth_index (Suc (Suc n)) r a
      (det (mat k k (\<lambda>(i,j).
        roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P))) +
    ereal (real k *
      (real (r (Suc n)) / real (r n)))"
    by (rule roth_tensor_det_index_lower[OF ip])
      (use half rp rl kn row in auto)
  have "ereal (real k * t^2 / (2 * real (Suc (Suc n)))) \<le>
    ereal (\<Sum>j<k. max 0
      (t - real j / real (r (Suc n))))"
    using num by simp
  then show ?thesis using det by (rule order_trans)
qed

section \<open>Index attained inside the degree box\<close>

lemma roth_taylor_index_box:
  fixes P :: "rat mpoly"
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
    using box cp by (auto simp: roth_poly_in_box_def coeff_def in_keys_iff)
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

lemma roth_box_weight_le_dim:
  assumes box: "I \<in> roth_exponent_box m r"
    and pos: "\<And>v. v<m \<Longrightarrow> 0 < r v"
  shows "roth_weight m r I \<le> real m"
proof -
  have step: "real (Poly_Mapping.lookup I v) / real (r v) \<le> 1"
    if vm: "v<m" for v
    using roth_exponent_boxD(2)[OF box vm] pos[OF vm]
    by (simp add: divide_le_eq)
  have "roth_weight m r I \<le> (\<Sum>v<m. (1::real))"
    unfolding roth_weight_def
    by (rule sum_mono) (use step in auto)
  then show ?thesis by simp
qed

lemma roth_index_box_attained:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P"
    and nz: "P\<noteq>0"
    and pos: "\<And>v. v<m \<Longrightarrow> 0<r v"
  obtains t where "roth_index m r a P = ereal t"
    "0\<le>t" "t\<le>real m"
proof -
  obtain I where tc: "roth_taylor_coeff a I P \<noteq> 0"
    and ip: "roth_index m r a P = ereal (roth_weight m r I)"
    using roth_index_attained[OF nz] by blast
  have ibox: "I\<in>roth_exponent_box m r"
    by (rule roth_taylor_index_box[OF box tc])
  have w: "roth_weight m r I \<le> real m"
    by (rule roth_box_weight_le_dim[OF ibox]) (rule pos)
  show thesis
    by (rule that[OF ip roth_weight_nonneg w])
qed

lemma roth_halving_positive_all:
  fixes r :: "nat \<Rightarrow> nat"
  assumes half: "\<And>v. Suc v < Suc (Suc n) \<Longrightarrow>
      2 * r (Suc v) \<le> r v"
    and rp: "0<r n" and rl: "0<r (Suc n)"
    and vm: "v < Suc (Suc n)"
  shows "0<r v"
proof (cases "v = Suc n")
  case True
  then show ?thesis using rl by simp
next
  case False
  then have vn: "v\<le>n" using vm by arith
  have le: "r n \<le> r v"
    by (rule roth_halving_antitone
      [where r=r and m="Suc (Suc n)" and u=v and v=n])
      (use half vn in auto)
  show ?thesis using rp le by arith
qed

theorem roth_tensor_det_index_quadratic_box:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box (Suc (Suc n)) r P"
    and nz: "P\<noteq>0"
    and half: "\<And>v. Suc v < Suc (Suc n) \<Longrightarrow>
      2 * r (Suc v) \<le> r v"
    and rp: "0<r n" and rl: "0<r (Suc n)"
    and kn: "k \<le> Suc (r (Suc n))"
    and row: "\<And>i. i<k \<Longrightarrow>
      Poly_Mapping.keys (mu i) \<subseteq> {..<Suc n} \<and>
      roth_total_order (Suc n) (mu i) \<le> i"
  shows "ereal (real k *
      (real_of_ereal (roth_index (Suc (Suc n)) r a P))^2 /
        (2 * real (Suc (Suc n)))) \<le>
    roth_index (Suc (Suc n)) r a
      (det (mat k k (\<lambda>(i,j).
        roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P))) +
    ereal (real k *
      (real (r (Suc n)) / real (r n)))"
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


end
