theory Roth_Kronecker_Expansion
  imports Roth_Kronecker_Jet
begin

section \<open>Uniform expansion of higher substituted derivatives\<close>

definition roth_total_order :: "nat \<Rightarrow> (nat,nat) poly_mapping \<Rightarrow> nat" where
  "roth_total_order m J = (\<Sum>v<m. Poly_Mapping.lookup J v)"

lemma roth_total_order_add:
  "roth_total_order m (I+J) =
    roth_total_order m I + roth_total_order m J"
  by (simp add: roth_total_order_def lookup_add sum.distrib)

lemma roth_total_order_single:
  assumes "v<m"
  shows "roth_total_order m (Poly_Mapping.single v 1) = 1"
  using assms
  by (simp add: roth_total_order_def lookup_single when_def
    sum.remove[of "{..<m}" v])

fun roth_jet_index :: "nat option list \<Rightarrow> (nat,nat) poly_mapping" where
  "roth_jet_index [] = 0"
| "roth_jet_index (None # xs) = roth_jet_index xs"
| "roth_jet_index (Some v # xs) =
    roth_jet_index xs + Poly_Mapping.single v 1"

definition roth_jet_alphabet :: "nat \<Rightarrow> nat option set" where
  "roth_jet_alphabet m = insert None (Some ` {..<m})"

definition roth_jet_words :: "nat \<Rightarrow> nat \<Rightarrow> nat option list set" where
  "roth_jet_words m i =
    {xs. set xs \<subseteq> roth_jet_alphabet m \<and> length xs = i}"

lemma finite_roth_jet_words [simp]:
  "finite (roth_jet_words m i)"
  by (simp add: roth_jet_words_def roth_jet_alphabet_def
    finite_lists_length_eq)

lemma roth_jet_words_zero [simp]:
  "roth_jet_words m 0 = {[]}"
  by (auto simp: roth_jet_words_def)

lemma roth_jet_index_order:
  assumes "set xs \<subseteq> roth_jet_alphabet m"
  shows "roth_total_order m (roth_jet_index xs) \<le> length xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by (simp add: roth_total_order_def)
next
  case (Cons a xs)
  show ?case
  proof (cases a)
    case None
    then show ?thesis using Cons
      by (simp add: roth_jet_alphabet_def)
  next
    case (Some v)
    then have vm: "v<m"
      using Cons.prems by (auto simp: roth_jet_alphabet_def)
    have t: "roth_total_order m (Poly_Mapping.single v 1) = 1"
      by (rule roth_total_order_single[OF vm])
    show ?thesis using Cons.IH Cons.prems t Some
      by (simp add: roth_total_order_add roth_jet_alphabet_def)
  qed
qed

lemma roth_nat_keys_add:
  fixes I J :: "(nat,nat) poly_mapping"
  shows "Poly_Mapping.keys (I+J) \<subseteq>
    Poly_Mapping.keys I \<union> Poly_Mapping.keys J"
proof (rule subsetI)
  fix v
  assume h: "v \<in> Poly_Mapping.keys (I+J)"
  show "v \<in> Poly_Mapping.keys I \<union> Poly_Mapping.keys J"
  proof (rule ccontr)
    assume "v \<notin> Poly_Mapping.keys I \<union> Poly_Mapping.keys J"
    then have a: "Poly_Mapping.lookup I v = 0"
      and b: "Poly_Mapping.lookup J v = 0"
      by (simp_all add: not_in_keys_iff_lookup_eq_zero)
    have "Poly_Mapping.lookup (I+J) v = 0"
      by (simp add: lookup_add a b)
    then show False using h by (simp add: in_keys_iff)
  qed
qed

lemma roth_jet_index_support:
  assumes "set xs \<subseteq> roth_jet_alphabet m"
  shows "Poly_Mapping.keys (roth_jet_index xs) \<subseteq> {..<m}"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases a)
      (auto simp: roth_jet_alphabet_def
        dest: subsetD[OF roth_nat_keys_add])
qed

lemma roth_jet_word_bounds:
  assumes h: "xs \<in> roth_jet_words m i"
  shows "Poly_Mapping.keys (roth_jet_index xs) \<subseteq> {..<m}"
    "roth_total_order m (roth_jet_index xs) \<le> i"
proof -
  have s: "set xs \<subseteq> roth_jet_alphabet m"
    and len: "length xs = i"
    using h by (auto simp: roth_jet_words_def)
  show "Poly_Mapping.keys (roth_jet_index xs) \<subseteq> {..<m}"
    by (rule roth_jet_index_support[OF s])
  show "roth_total_order m (roth_jet_index xs) \<le> i"
    using roth_jet_index_order[OF s] len by simp
qed

lemma roth_jet_words_Suc:
  "roth_jet_words m (Suc i) =
    ((#) None ` roth_jet_words m i) \<union>
      ((\<lambda>(xs,v). Some v # xs) ` (roth_jet_words m i \<times> {..<m}))"
  by (auto simp: roth_jet_words_def roth_jet_alphabet_def
    length_Suc_conv)

lemma roth_sum_jet_words:
  fixes f :: "nat option list \<Rightarrow> rat poly"
  shows "(\<Sum>ys\<in>roth_jet_words m (Suc i). f ys) =
    (\<Sum>xs\<in>roth_jet_words m i. f (None#xs)) +
    (\<Sum>xs\<in>roth_jet_words m i. \<Sum>v<m. f (Some v#xs))"
proof -
  let ?S = "roth_jet_words m i"
  let ?A = "((#) None ` ?S)"
  let ?C = "((\<lambda>(xs,v). Some v#xs) ` (?S \<times> {..<m}))"
  have disj: "?A \<inter> ?C = {}" by auto
  have a: "(\<Sum>ys\<in>?A. f ys) = (\<Sum>xs\<in>?S. f (None#xs))"
    by (subst sum.reindex) (auto simp: inj_on_def)
  have c: "(\<Sum>ys\<in>?C. f ys) =
    (\<Sum>xs\<in>?S. \<Sum>v<m. f (Some v#xs))"
    by (subst sum.reindex)
      (auto simp: inj_on_def sum.cartesian_product split_def)
  show ?thesis using a c disj
    by (simp add: roth_jet_words_Suc sum.union_disjoint)
qed

fun roth_jet_coeff :: "nat \<Rightarrow> nat \<Rightarrow> nat option list \<Rightarrow> rat poly"
  where
  "roth_jet_coeff B 0 xs = (if xs=[] then 1 else 0)"
| "roth_jet_coeff B (Suc i) [] = 0"
| "roth_jet_coeff B (Suc i) (None#xs) =
    pderiv (roth_jet_coeff B i xs)"
| "roth_jet_coeff B (Suc i) (Some v#xs) =
    roth_jet_coeff B i xs *
      Polynomial.monom
        (of_nat (B^v * Suc (Poly_Mapping.lookup (roth_jet_index xs) v)))
        (B^v-1)"

lemma roth_jet_expansion:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box m r P" and B: "0<B"
  shows "(pderiv ^^ i) (roth_ksubst m B P) =
    (\<Sum>xs\<in>roth_jet_words m i.
      roth_jet_coeff B i xs *
        roth_ksubst m B (roth_hasse (roth_jet_index xs) P))"
  using box B
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then show ?case
    by (simp add: funpow_Suc_right roth_poly_pderiv_sum
      roth_ksubst_hasse_weighted_deriv roth_sum_jet_words
      sum.distrib)
qed

end
