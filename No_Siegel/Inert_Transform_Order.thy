theory Inert_Transform_Order
  imports Inert_Rows
begin

declare [[apply_timeout = 20]]

lemma green_row_order_nth_index:
  assumes r: "r < R" and s: "s < S"
  shows "r*S+s < length (green_row_order R S)"
    and "green_row_order R S ! (r*S+s) = (r,s)"
proof -
  have pos: "0 < S" using s by linarith
  have lt: "r*S+s < R*S"
  proof -
    have "r*S+s < (r+1)*S" using s by (simp add: algebra_simps)
    also have "... \<le> R*S" using r by (intro mult_right_mono; simp)
    finally show ?thesis .
  qed
  show "r*S+s < length (green_row_order R S)" using lt by simp
  show "green_row_order R S ! (r*S+s) = (r,s)"
    using lt r s pos
    by (simp add: green_row_order_def product_nth)
qed

lemma green_row_order_nth_components:
  assumes a: "a < R*S"
  shows "green_row_order R S ! a = (a div S, a mod S)"
proof -
  have S: "0 < S" using a by (cases S) auto
  have "a < length (green_row_order R S)" using a by simp
  then show ?thesis
  proof -
    have ar: "a div S < R" using a S by (simp add: div_less_iff_less_mult)
    have as: "a mod S < S" using S by simp
    show ?thesis using a ar as
      by (simp add: green_row_order_def product_nth)
  qed
qed

lemma green_inert_lower_row_index:
  assumes p: "0 < p" and r: "r < R" and s: "s < S"
    and i: "0 < i" "i \<le> green_inert_h p S (r,s)"
    and b: "b = (r-p*i)*S+(s+i)"
    and a: "a = r*S+s"
  shows "b < a" "green_row_order R S ! b = (r-p*i,s+i)"
proof -
  have rr: "r-p*i < r" and ss: "s+i < S"
    by (rule green_inert_h_lower_row[OF p s i(1) i(2)])+
  have rpi: "r-p*i < R" using rr r by linarith
  have bR: "b < length (green_row_order R S)" and brow:
    "green_row_order R S ! b = (r-p*i,s+i)"
    unfolding b by (rule green_row_order_nth_index[OF rpi ss])+
  show "green_row_order R S ! b = (r-p*i,s+i)" by (rule brow)
  have "b < (r-p*i+1)*S"
    unfolding b using ss by (simp add: algebra_simps)
  also have "... \<le> r*S" using rr by (intro mult_right_mono; simp)
  also have "... \<le> a" unfolding a by simp
  finally show "b < a" .
qed

lemma green_row_order_nth_bounds:
  assumes a: "a < R*S"
  shows "fst (green_row_order R S ! a) < R"
    and "snd (green_row_order R S ! a) < S"
proof -
  have al: "a < length (green_row_order R S)" using a by simp
  have mem: "green_row_order R S ! a \<in> green_row_indices R S"
    using nth_mem[OF al] by simp
  then show "fst (green_row_order R S ! a) < R"
    "snd (green_row_order R S ! a) < S"
    by (auto simp: green_row_indices_def)
qed

lemma green_row_order_nth_index_eq:
  assumes a: "a < R*S"
  shows "a = fst (green_row_order R S ! a)*S +
    snd (green_row_order R S ! a)"
  using green_row_order_nth_components[OF a]
    div_mult_mod_eq[of a S]
  by (simp add: mult.commute)

definition green_row_transform_matrix ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int mat" where
  "green_row_transform_matrix p R S =
    mat (R*S) (R*S) (\<lambda>(a,b).
      let (r,s) = green_row_order R S ! a;
          h = green_inert_h p S (r,s)
      in if a=b then 1 else
        (\<Sum>i\<in>{1..h}. if b=(r-p*i)*S+(s+i)
           then (-1::int)^i * int (h choose i) else 0))"

lemma green_row_transform_matrix_carrier [simp]:
  "green_row_transform_matrix p R S \<in> carrier_mat (R*S) (R*S)"
  by (simp add: green_row_transform_matrix_def)

lemma green_row_transform_matrix_diag:
  assumes a: "a < R*S"
  shows "green_row_transform_matrix p R S $$ (a,a) = 1"
  using a by (simp add: green_row_transform_matrix_def Let_def
    split: prod.splits)

lemma green_row_transform_matrix_lower:
  assumes p: "0 < p" and ab: "a < b" and b: "b < R*S"
  shows "green_row_transform_matrix p R S $$ (a,b) = 0"
proof -
  have a: "a < R*S" using ab b by linarith
  let ?r = "fst (green_row_order R S ! a)"
  let ?s = "snd (green_row_order R S ! a)"
  let ?h = "green_inert_h p S (?r,?s)"
  have r: "?r < R" and s: "?s < S"
    by (rule green_row_order_nth_bounds[OF a])+
  have ae: "a = ?r*S+?s" by (rule green_row_order_nth_index_eq[OF a])
  have neq: "b \<noteq> (?r-p*i)*S+(?s+i)" if i: "i \<in> {1..?h}" for i
  proof
    assume be: "b = (?r-p*i)*S+(?s+i)"
    have ipos: "0 < i" and ih: "i \<le> ?h" using i by auto
    have "b < a"
      by (rule green_inert_lower_row_index(1)[OF p r s ipos ih be ae])
    with ab show False by linarith
  qed
  have sumzero: "(\<Sum>i\<in>{1..?h}. if b=(?r-p*i)*S+(?s+i)
    then (-1::int)^i * int (?h choose i) else 0) = 0"
    by (rule sum.neutral) (use neq in auto)
  have row: "green_row_order R S ! a = (?r,?s)" by simp
  have ne: "a \<noteq> b" using ab by simp
  have entry: "green_row_transform_matrix p R S $$ (a,b) =
      (\<Sum>i\<in>{1..?h}. if b=(?r-p*i)*S+(?s+i)
        then (-1::int)^i * int (?h choose i) else 0)"
    using a b ne
    by (simp only: green_row_transform_matrix_def index_mat
      case_prod_beta Let_def fst_conv snd_conv if_False)
  show ?thesis using entry sumzero by simp
qed

lemma green_row_transform_matrix_det:
  assumes p: "0 < p"
  shows "det (green_row_transform_matrix p R S) = 1"
proof -
  let ?U = "green_row_transform_matrix p R S"
  have tri: "det ?U = prod_list (diag_mat ?U)"
    by (rule det_lower_triangular[OF _ green_row_transform_matrix_carrier])
      (use green_row_transform_matrix_lower[OF p] in auto)
  have diag: "(\<Prod>i=0..<R*S. ?U $$ (i,i)) = (1::int)"
    by (rule trans[OF prod.cong[OF refl]])
      (auto simp: green_row_transform_matrix_diag)
  have dims: "dim_row ?U = R*S"
    by (simp add: green_row_transform_matrix_def)
  show ?thesis
    using tri diag by (simp add: prod_list_diag_prod dims)
qed

lemma green_row_transform_matrix_action:
  fixes f :: "nat \<Rightarrow> int"
  assumes p: "0 < p" and a: "a < R*S"
    and k: "k = green_row_order R S ! a"
    and h: "h = green_inert_h p S k"
  shows "(\<Sum>b<R*S. green_row_transform_matrix p R S $$ (a,b) * f b) =
    f a + (\<Sum>i\<in>{1..h}.
      ((-1::int)^i * int (h choose i)) *
        f ((fst k-p*i)*S+(snd k+i)))"
proof -
  let ?U = "green_row_transform_matrix p R S"
  let ?r = "fst k"
  let ?s = "snd k"
  let ?c = "\<lambda>i. (-1::int)^i * int (h choose i)"
  let ?b = "\<lambda>i. (?r-p*i)*S+(?s+i)"
  have r: "?r < R" and s: "?s < S"
    unfolding k by (rule green_row_order_nth_bounds[OF a])+
  have ae: "a = ?r*S+?s"
    unfolding k by (rule green_row_order_nth_index_eq[OF a])
  have lower: "?b i < a" if i: "i \<in> {1..h}" for i
  proof -
    have ipos: "0 < i" using i by simp
    have ih: "i \<le> green_inert_h p S (?r,?s)"
      using i h by simp
    show ?thesis
      by (rule green_inert_lower_row_index(1)[OF p r s ipos ih refl ae])
  qed
  have bbound: "?b i < R*S" if i: "i \<in> {1..h}" for i
    using lower[OF i] a by linarith
  have ne: "a \<noteq> ?b i" if i: "i \<in> {1..h}" for i
    using lower[OF i] by linarith
  have diagzero: "(\<Sum>i\<in>{1..h}. if a=?b i then ?c i else 0) = 0"
    by (rule sum.neutral; use ne in simp)
  have entry: "?U $$ (a,b) =
      (if a=b then 1 else 0) +
      (\<Sum>i\<in>{1..h}. if b=?b i then ?c i else 0)"
    if b: "b < R*S" for b
  proof -
    obtain rr ss where kk: "k = (rr,ss)" by (cases k) auto
    have row: "green_row_order R S ! a = (rr,ss)"
      using k kk by simp
    have hh: "h = green_inert_h p S (rr,ss)"
      using h kk by simp
    have raw: "?U $$ (a,b) =
      (if a=b then 1 else
        (\<Sum>i\<in>{1..green_inert_h p S (rr,ss)}.
          if b=(rr-p*i)*S+(ss+i)
          then (-1::int)^i *
            int (green_inert_h p S (rr,ss) choose i) else 0))"
      using a b
      by (simp add: green_row_transform_matrix_def row Let_def)
    have orig: "?U $$ (a,b) =
      (if a=b then 1 else
        (\<Sum>i\<in>{1..h}. if b=?b i then ?c i else 0))"
      unfolding hh kk
      by (simp only: fst_conv snd_conv raw)
    show ?thesis
      using orig diagzero by (cases "a=b") simp_all
  qed
  have singled: "(\<Sum>b<R*S.
      (if b=?b i then ?c i else 0) * f b) = ?c i * f (?b i)"
    if i: "i \<in> {1..h}" for i
  proof -
    have mem: "?b i \<in> {..<R*S}" using bbound[OF i] by simp
    have zero: "(\<Sum>b\<in>{..<R*S}-{?b i}.
        (if b=?b i then ?c i else 0) * f b) = 0"
      by (rule sum.neutral; simp)
    have "(\<Sum>b<R*S. (if b=?b i then ?c i else 0) * f b) =
        (if ?b i=?b i then ?c i else 0) * f (?b i) +
        (\<Sum>b\<in>{..<R*S}-{?b i}.
          (if b=?b i then ?c i else 0) * f b)"
      by (rule sum.remove; use mem in simp)
    then show ?thesis using zero by simp
  qed
  have diag: "(\<Sum>b<R*S. (if a=b then 1 else 0) * f b) = f a"
  proof -
    have mem: "a \<in> {..<R*S}" using a by simp
    have zero: "(\<Sum>b\<in>{..<R*S}-{a}.
        (if a=b then 1 else 0) * f b) = 0"
      by (rule sum.neutral; simp)
    have "(\<Sum>b<R*S. (if a=b then 1 else 0) * f b) =
        (if a=a then 1 else 0) * f a +
        (\<Sum>b\<in>{..<R*S}-{a}. (if a=b then 1 else 0) * f b)"
      by (rule sum.remove; use mem in simp)
    then show ?thesis using zero by simp
  qed
  have swap: "(\<Sum>b<R*S. \<Sum>i\<in>{1..h}.
      (if b=?b i then ?c i else 0) * f b) =
    (\<Sum>i\<in>{1..h}. \<Sum>b<R*S.
      (if b=?b i then ?c i else 0) * f b)"
    by (rule sum.swap)
  have "(\<Sum>b<R*S. ?U $$ (a,b) * f b) =
      (\<Sum>b<R*S. ((if a=b then 1 else 0) +
        (\<Sum>i\<in>{1..h}. if b=?b i then ?c i else 0)) * f b)"
    by (rule sum.cong[OF refl]) (use entry in auto)
  also have "... =
      (\<Sum>b<R*S. (if a=b then 1 else 0) * f b) +
      (\<Sum>b<R*S. (\<Sum>i\<in>{1..h}.
        (if b=?b i then ?c i else 0) * f b))"
    by (simp only: distrib_right sum_distrib_right sum.distrib)
  also have "... = f a + (\<Sum>i\<in>{1..h}.
      (\<Sum>b<R*S. (if b=?b i then ?c i else 0) * f b))"
    using diag swap by simp
  also have "... = f a + (\<Sum>i\<in>{1..h}. ?c i * f (?b i))"
    by (rule arg_cong[where f="\<lambda>x. f a + x"])
      (rule sum.cong[OF refl], rule singled, assumption)
  finally show ?thesis .
qed

lemma green_row_transform_matrix_action_binomial:
  fixes f :: "nat \<Rightarrow> int"
  assumes p: "0 < p" and a: "a < R*S"
    and k: "k = green_row_order R S ! a"
    and h: "h = green_inert_h p S k"
  shows "(\<Sum>b<R*S. green_row_transform_matrix p R S $$ (a,b) * f b) =
    (\<Sum>i\<le>h. ((-1::int)^i * int (h choose i)) *
      f ((fst k-p*i)*S+(snd k+i)))"
proof -
  let ?g = "\<lambda>i. ((-1::int)^i * int (h choose i)) *
      f ((fst k-p*i)*S+(snd k+i))"
  have action: "(\<Sum>b<R*S.
      green_row_transform_matrix p R S $$ (a,b) * f b) =
    f a + (\<Sum>i\<in>{1..h}. ?g i)"
    by (rule green_row_transform_matrix_action[OF p a k h])
  have aindex: "a = fst k*S+snd k"
    unfolding k by (rule green_row_order_nth_index_eq[OF a])
  have zero: "?g 0 = f a" using aindex by simp
  have split: "(\<Sum>i\<le>h. ?g i) = ?g 0 + (\<Sum>i\<in>{1..h}. ?g i)"
  proof -
    have eq: "{..h} - {0} = {1..h}" by auto
    have "(\<Sum>i\<le>h. ?g i) =
        ?g 0 + (\<Sum>i\<in>{..h}-{0}. ?g i)"
      by (rule sum.remove) simp_all
    then show ?thesis by (simp only: eq)
  qed
  show ?thesis using action split zero by simp
qed

declare [[apply_timeout = 0]]

end
