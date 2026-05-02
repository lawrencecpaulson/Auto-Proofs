theory Infinite_Product
  imports "HOL-Complex_Analysis.Complex_Analysis"
begin

definition HAS_SETPROD :: \<open>('a \<Rightarrow> 'b :: {semidom, topological_semigroup_mult, t2_space}) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool\<close> 
    where has_setprod_def: \<open>HAS_SETPROD f A x \<longleftrightarrow> (prod f \<longlongrightarrow> x) (finite_subsets_at_top A)\<close>

abbreviation has_setprod (infixr "has'_setprod" 46) where
  "(f has_setprod S) A \<equiv> HAS_SETPROD f A S"

definition multipliable_on :: "('a \<Rightarrow> 'b::{semidom, topological_semigroup_mult, t2_space}) \<Rightarrow> 'a set \<Rightarrow> bool" (infixr "multipliable'_on" 46) where
  "f multipliable_on A \<equiv> (\<exists>x. (f has_setprod x) A)"

definition infprod :: "('a \<Rightarrow> 'b::{semidom,topological_semigroup_mult,t2_space, t2_space}) \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "infprod f A = (if f multipliable_on A then Lim (finite_subsets_at_top A) (prod f) else 1)"

definition abs_multipliable_on :: "('a \<Rightarrow> 'b::real_normed_algebra_1) \<Rightarrow> 'a set \<Rightarrow> bool" (infixr "abs'_multipliable'_on" 46) where
  "f abs_multipliable_on A \<longleftrightarrow> (\<lambda>x. 1 + norm (f x - 1)) multipliable_on A"

syntax (ASCII)
  "_infprod" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::topological_comm_monoid_mult"  ("(3INFPROD (_/:_)./ _)" [0, 51, 10] 10)
syntax
  "_infprod" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::topological_comm_monoid_mult"  ("(2\<Prod>\<^sub>\<infinity>(_/\<in>_)./ _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Prod>\<^sub>\<infinity>i\<in>A. b" \<rightleftharpoons> "CONST infprod (\<lambda>i. b) A"

syntax (ASCII)
  "_univinfprod" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a"  ("(3INFPROD _./ _)" [0, 10] 10)
syntax
  "_univinfprod" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<Prod>\<^sub>\<infinity>_./ _)" [0, 10] 10)
translations
  "\<Prod>\<^sub>\<infinity>x. t" \<rightleftharpoons> "CONST infprod (\<lambda>x. t) (CONST UNIV)"

syntax (ASCII)
  "_qinfprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(3INFPROD _ |/ _./ _)" [0, 0, 10] 10)
syntax
  "_qinfprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<Prod>\<^sub>\<infinity>_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<Prod>\<^sub>\<infinity>x|P. t" => "CONST infprod (\<lambda>x. t) {x. P}"

print_translation \<open>
let
  fun prod_tr' [Abs (x, Tx, t), Const (@{const_syntax Collect}, _) $ Abs (y, Ty, P)] =
        if x <> y then raise Match
        else
          let
            val x' = Syntax_Trans.mark_bound_body (x, Tx);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in
            Syntax.const @{syntax_const "_qinfprod"} $ Syntax_Trans.mark_bound_abs (x, Tx) $ P' $ t'
          end
    | prod_tr' _ = raise Match;
in [(@{const_syntax infprod}, K prod_tr')] end
\<close>

subsection \<open>General properties\<close>

lemma filterlim_Un_finite_subsets_at_top:
  assumes "finite Y"
  shows   "filterlim (\<lambda>X. X \<union> Y) (finite_subsets_at_top (X \<union> Y)) (finite_subsets_at_top X)"
  unfolding filterlim_def le_filter_def eventually_filtermap
proof safe
  fix P :: "'a set \<Rightarrow> bool"
  assume "\<forall>\<^sub>F A in finite_subsets_at_top (X \<union> Y). P A"
  then obtain A where A: "finite A" "A \<subseteq> X \<union> Y" "\<And>Z. finite Z \<Longrightarrow> A \<subseteq> Z \<Longrightarrow> Z \<subseteq> X \<union> Y \<Longrightarrow> P Z"
    unfolding eventually_finite_subsets_at_top by metis
  show "\<forall>\<^sub>F A in finite_subsets_at_top X. P (A \<union> Y)"
    unfolding eventually_finite_subsets_at_top
  proof (rule exI[of _ "A - Y"], intro allI conjI impI)
    show "finite (A - Y)" and "A - Y \<subseteq> X"
      using assms A(1,2) by auto
  next
    fix Z assume Z: "finite Z \<and> A - Y \<subseteq> Z \<and> Z \<subseteq> X"
    show "P (Z \<union> Y)"
      by (rule A) (use Z assms in auto)
  qed
qed

lemma has_setprod_cong_neutral:
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 1\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 1\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows "(f has_setprod x) S \<longleftrightarrow> (g has_setprod x) T"
proof -
  have \<open>eventually P (filtermap (prod f) (finite_subsets_at_top S))
      = eventually P (filtermap (prod g) (finite_subsets_at_top T))\<close> for P
  proof 
    assume \<open>eventually P (filtermap (prod f) (finite_subsets_at_top S))\<close>
    then obtain F0 where \<open>finite F0\<close> and \<open>F0 \<subseteq> S\<close> and F0_P: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> F \<supseteq> F0 \<Longrightarrow> P (prod f F)\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
    define F0' where \<open>F0' = F0 \<inter> T\<close>
    have [simp]: \<open>finite F0'\<close> \<open>F0' \<subseteq> T\<close>
      by (simp_all add: F0'_def \<open>finite F0\<close>)
    have \<open>P (prod g F)\<close> if \<open>finite F\<close> \<open>F \<subseteq> T\<close> \<open>F \<supseteq> F0'\<close> for F
    proof -
      have \<open>P (prod f ((F\<inter>S) \<union> (F0\<inter>S)))\<close>
        by (intro F0_P) (use \<open>F0 \<subseteq> S\<close> \<open>finite F0\<close> that in auto)
      also have \<open>prod f ((F\<inter>S) \<union> (F0\<inter>S)) = prod g F\<close>
        by (intro prod.mono_neutral_cong) (use that \<open>finite F0\<close> F0'_def assms in auto)
      finally show ?thesis .
    qed
    with \<open>F0' \<subseteq> T\<close> \<open>finite F0'\<close> show \<open>eventually P (filtermap (prod g) (finite_subsets_at_top T))\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
  next
    assume \<open>eventually P (filtermap (prod g) (finite_subsets_at_top T))\<close>
    then obtain F0 where \<open>finite F0\<close> and \<open>F0 \<subseteq> T\<close> and F0_P: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> T \<Longrightarrow> F \<supseteq> F0 \<Longrightarrow> P (prod g F)\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
    define F0' where \<open>F0' = F0 \<inter> S\<close>
    have [simp]: \<open>finite F0'\<close> \<open>F0' \<subseteq> S\<close>
      by (simp_all add: F0'_def \<open>finite F0\<close>)
    have \<open>P (prod f F)\<close> if \<open>finite F\<close> \<open>F \<subseteq> S\<close> \<open>F \<supseteq> F0'\<close> for F
    proof -
      have \<open>P (prod g ((F\<inter>T) \<union> (F0\<inter>T)))\<close>
        by (intro F0_P) (use \<open>F0 \<subseteq> T\<close> \<open>finite F0\<close> that in auto)
      also have \<open>prod g ((F\<inter>T) \<union> (F0\<inter>T)) = prod f F\<close>
        by (intro prod.mono_neutral_cong) (use that \<open>finite F0\<close> F0'_def assms in auto)
      finally show ?thesis .
    qed
    with \<open>F0' \<subseteq> S\<close> \<open>finite F0'\<close> show \<open>eventually P (filtermap (prod f) (finite_subsets_at_top S))\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
  qed

  then have tendsto_x: "(prod f \<longlongrightarrow> x) (finite_subsets_at_top S) \<longleftrightarrow> (prod g \<longlongrightarrow> x) (finite_subsets_at_top T)" for x
    by (simp add: le_filter_def filterlim_def)

  then show ?thesis
    by (simp add: has_setprod_def)
qed

lemma has_setprod_cong: 
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "(f has_setprod x) A \<longleftrightarrow> (g has_setprod x) A"
  using assms by (intro has_setprod_cong_neutral) auto

lemma has_setprod_mult:
  assumes \<open>(f has_setprod a) A\<close>
  assumes \<open>(g has_setprod b) A\<close>
  shows \<open>((\<lambda>x. f x * g x) has_setprod (a * b)) A\<close>
proof -
  from assms have lim_f: \<open>(prod f \<longlongrightarrow> a)  (finite_subsets_at_top A)\<close>
    and lim_g: \<open>(prod g \<longlongrightarrow> b)  (finite_subsets_at_top A)\<close>
    by (simp_all add: has_setprod_def)
  then have lim: \<open>(prod (\<lambda>x. f x * g x) \<longlongrightarrow> a * b) (finite_subsets_at_top A)\<close>
    unfolding prod.distrib by (rule tendsto_mult)
  then show ?thesis using assms
    by (simp_all add: has_setprod_def)
qed

lemma has_setprod_Un_disjoint:
  assumes "(f has_setprod a) A"
  assumes "(f has_setprod b) B"
  assumes disj: "A \<inter> B = {}"
  shows \<open>(f has_setprod (a * b)) (A \<union> B)\<close>
proof -
  define fA fB where \<open>fA x = (if x \<in> A then f x else 1)\<close>
    and \<open>fB x = (if x \<notin> A then f x else 1)\<close> for x
  have "(f has_setprod a) A \<longleftrightarrow> (fA has_setprod a) (A \<union> B)"
    by (intro has_setprod_cong_neutral) (auto simp: fA_def)
  with assms(1) have fA: \<open>(fA has_setprod a) (A \<union> B)\<close>
    by blast
  have "(f has_setprod b) B \<longleftrightarrow> (fB has_setprod b) (A \<union> B)"
    using disj by (intro has_setprod_cong_neutral) (auto simp: fB_def)
  with assms(2) have fB: \<open>(fB has_setprod b) (A \<union> B)\<close>
    by blast
  have fAB: \<open>f x = fA x * fB x\<close> for x
    unfolding fA_def fB_def by simp
  show ?thesis
    unfolding fAB
    using fA fB by (rule has_setprod_mult)
qed

lemma has_setprodI:
  assumes "((\<lambda>X. \<Prod>x\<in>X. f x) \<longlongrightarrow> P) (finite_subsets_at_top A)"
  shows   "(f has_setprod P) A"
  using assms unfolding has_setprod_def .

lemma has_setprodD:
  assumes "(f has_setprod P) A"
  shows   "((\<lambda>X. \<Prod>x\<in>X. f x) \<longlongrightarrow> P) (finite_subsets_at_top A)"
  using assms unfolding has_setprod_def .

lemma has_setprod_finite:
  assumes "finite A"
  shows   "(f has_setprod (\<Prod>x\<in>A. f x)) A"
  using assms by (auto simp: finite_subsets_at_top_finite has_setprod_def principal_eq_bot_iff)

lemma has_setprod_unique: "(f has_setprod P) A \<Longrightarrow> (f has_setprod P') A \<Longrightarrow> P = P'"
  using has_setprodD tendsto_unique finite_subsets_at_top_neq_bot by metis

lemma has_setprod_finite_iff [simp]:
  assumes "finite A"
  shows   "(f has_setprod P) A \<longleftrightarrow> P = (\<Prod>x\<in>A. f x)"
  using has_setprod_finite assms has_setprod_unique by fast

lemma infprodI:
  assumes \<open>(f has_setprod x) A\<close>
  shows \<open>infprod f A = x\<close>
  using has_setprodD[OF assms] assms unfolding infprod_def multipliable_on_def
  by (meson finite_subsets_at_top_neq_bot tendsto_Lim)

lemma infprod_eqI:
  fixes f g :: \<open>'a \<Rightarrow> 'b::{semidom, topological_semigroup_mult, t2_space}\<close>
  assumes \<open>x = y\<close>
  assumes \<open>(f has_setprod x) A\<close>
  assumes \<open>(g has_setprod y) B\<close>
  shows \<open>infprod f A = infprod g B\<close>
  using assms infprodI by blast

lemma infprod_eqI':
  fixes f g :: \<open>'a \<Rightarrow> 'b::{semidom, topological_semigroup_mult, t2_space}\<close>
  assumes \<open>\<And>x. (f has_setprod x) A \<longleftrightarrow> (g has_setprod x) B\<close>
  shows \<open>infprod f A = infprod g B\<close>
  by (metis assms infprod_def infprod_eqI multipliable_on_def)

lemma infprod_not_exists:
  fixes f :: \<open>'a \<Rightarrow> 'b::{semidom, topological_semigroup_mult, t2_space}\<close>
  assumes \<open>\<not> f multipliable_on A\<close>
  shows \<open>infprod f A = 1\<close>
  by (simp add: assms infprod_def)

lemma multipliable_iff_has_setprod_infprod: "f multipliable_on A \<longleftrightarrow> (f has_setprod (infprod f A)) A"
  using infprodI multipliable_on_def by metis

lemma has_setprod_infprod[simp]:
  assumes \<open>f multipliable_on S\<close>
  shows \<open>(f has_setprod (infprod f S)) S\<close>
  using assms multipliable_iff_has_setprod_infprod by blast

lemma multipliable_on_cong_neutral: 
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 1\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 1\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows "f multipliable_on S \<longleftrightarrow> g multipliable_on T"
  using has_setprod_cong_neutral[of T S g f, OF assms]
  by (simp add: multipliable_on_def)

lemma infprod_cong_neutral: 
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 1\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 1\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows \<open>infprod f S = infprod g T\<close>
  by (smt (verit, best) assms has_setprod_cong_neutral infprod_eqI')

lemma multipliable_on_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "f multipliable_on A \<longleftrightarrow> g multipliable_on A"
  by (metis assms multipliable_on_def has_setprod_cong)

lemma infprod_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infprod f A = infprod g A"
  using assms infprod_eqI' has_setprod_cong by blast


lemma multipliable_on_cofin_subset:
  fixes f :: \<open>'a \<Rightarrow> 'b::real_normed_field\<close>
  assumes "f multipliable_on A" and "finite F" and "\<And>x. x \<in> F \<Longrightarrow> f x \<noteq> 0"
  shows "f multipliable_on (A - F)"
proof -
  define G where \<open>G = A \<inter> F\<close>
  have G_fin: \<open>finite G\<close>
    using assms(2) unfolding G_def by blast
  have G_sub: \<open>G \<subseteq> A\<close>
    unfolding G_def by blast
  have G_nz: \<open>prod f G \<noteq> 0\<close>
    unfolding G_def using assms(2,3)
    by (subst prod_zero_iff) auto
  from assms(1) obtain p where hp: \<open>(f has_setprod p) A\<close>
    unfolding multipliable_on_def by blast
  then have lim: \<open>(prod f \<longlongrightarrow> p) (finite_subsets_at_top A)\<close>
    unfolding has_setprod_def .
  have filt: \<open>filterlim (\<lambda>X. X \<union> G) (finite_subsets_at_top A) (finite_subsets_at_top (A - F))\<close>
    unfolding filterlim_def le_filter_def eventually_filtermap
  proof safe
    fix P assume \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. P X\<close>
    then obtain X0 where X0: \<open>finite X0\<close> \<open>X0 \<subseteq> A\<close>
        and X0_P: \<open>\<And>X. finite X \<Longrightarrow> X0 \<subseteq> X \<Longrightarrow> X \<subseteq> A \<Longrightarrow> P X\<close>
      unfolding eventually_finite_subsets_at_top by metis
    show \<open>\<forall>\<^sub>F X in finite_subsets_at_top (A - F). P (X \<union> G)\<close>
      unfolding eventually_finite_subsets_at_top
    proof (rule exI[of _ \<open>X0 - F\<close>], intro allI conjI impI)
      show \<open>finite (X0 - F)\<close> using X0(1) by blast
      show \<open>X0 - F \<subseteq> A - F\<close> using X0(2) by blast
    next
      fix X assume X: \<open>finite X \<and> X0 - F \<subseteq> X \<and> X \<subseteq> A - F\<close>
      have \<open>X0 \<subseteq> X \<union> G\<close>
        using X X0(2) unfolding G_def by blast
      moreover have \<open>X \<union> G \<subseteq> A\<close>
        using X G_sub by blast
      ultimately show \<open>P (X \<union> G)\<close>
        by (intro X0_P) (use X G_fin in auto)
    qed
  qed
  have ev_eq: \<open>\<forall>\<^sub>F X in finite_subsets_at_top (A - F). prod f (X \<union> G) = prod f X * prod f G\<close>
    unfolding eventually_finite_subsets_at_top
  proof (rule exI[of _ \<open>{}\<close>], intro allI conjI impI)
    fix X assume X: \<open>finite X \<and> {} \<subseteq> X \<and> X \<subseteq> A - F\<close>
    then have \<open>X \<inter> G = {}\<close> unfolding G_def by blast
    then show \<open>prod f (X \<union> G) = prod f X * prod f G\<close>
      using X G_fin by (subst prod.union_disjoint) auto
  qed auto
  have \<open>(prod f \<longlongrightarrow> p) (filtermap (\<lambda>X. X \<union> G) (finite_subsets_at_top (A - F)))\<close>
    using lim filt by (metis filterlim_def tendsto_mono)
  then have comp: \<open>((\<lambda>X. prod f (X \<union> G)) \<longlongrightarrow> p) (finite_subsets_at_top (A - F))\<close>
    by (subst (asm) tendsto_compose_filtermap[symmetric]) (simp add: o_def)
  have \<open>((\<lambda>X. prod f X * prod f G) \<longlongrightarrow> p) (finite_subsets_at_top (A - F))\<close>
    using comp ev_eq by (rule Lim_transform_eventually)
  then have \<open>((\<lambda>X. prod f X * prod f G) \<longlongrightarrow> (p / prod f G) * prod f G) (finite_subsets_at_top (A - F))\<close>
    by (simp add: G_nz)
  then have \<open>(prod f \<longlongrightarrow> p / prod f G) (finite_subsets_at_top (A - F))\<close>
    using G_nz by (subst (asm) tendsto_mult_right_iff)
  thus ?thesis
    unfolding multipliable_on_def has_setprod_def by blast
qed

lemma zero_imp_has_setprod_0:
  assumes "x \<in> A" "f x = 0"
  shows   "(f has_setprod 0) A"
proof -
  have "eventually (\<lambda>X. {x} \<subseteq> X \<and> finite X) (finite_subsets_at_top A)"
    unfolding eventually_finite_subsets_at_top using assms by force
  hence "eventually (\<lambda>X. prod f X = 0) (finite_subsets_at_top A)"
    by eventually_elim (use assms in auto)
  thus ?thesis
    unfolding has_setprod_def using tendsto_eventually by blast
qed  

lemma
  fixes a b :: "'a::real_normed_field"
  assumes \<open>(f has_setprod b) B\<close> and \<open>(f has_setprod a) A\<close> and AB: "A \<subseteq> B"
  assumes [simp]: "a \<noteq> 0"
  shows has_setprod_Diff: "(f has_setprod (b / a)) (B - A)"
proof -
  have nonzero: "f x \<noteq> 0" if "x \<in> A" for x
    using that assms(2) using zero_imp_has_setprod_0[of x A f] has_setprod_unique
    by fastforce
  have finite_subsets1:
    "finite_subsets_at_top (B - A) \<le> filtermap (\<lambda>F. F - A) (finite_subsets_at_top B)"
  proof (rule filter_leI)
    fix P assume "eventually P (filtermap (\<lambda>F. F - A) (finite_subsets_at_top B))"
    then obtain X where "finite X" and "X \<subseteq> B" 
      and P: "finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P (Y - A)" for Y
      unfolding eventually_filtermap eventually_finite_subsets_at_top by auto

    hence "finite (X-A)" and "X-A \<subseteq> B - A"
      by auto
    moreover have "finite Y \<and> X-A \<subseteq> Y \<and> Y \<subseteq> B - A \<longrightarrow> P Y" for Y
      using P[where Y="Y\<union>X"] \<open>finite X\<close> \<open>X \<subseteq> B\<close>
      by (metis Diff_subset Int_Diff Un_Diff finite_Un inf.orderE le_sup_iff sup.orderE sup_ge2)
    ultimately show "eventually P (finite_subsets_at_top (B - A))"
      unfolding eventually_finite_subsets_at_top by meson
  qed
  have finite_subsets2: 
    "filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B) \<le> finite_subsets_at_top A"
    apply (rule filter_leI)
      using assms unfolding eventually_filtermap eventually_finite_subsets_at_top
      by (metis Int_subset_iff finite_Int inf_le2 subset_trans)

  from assms(1) have limB: "(prod f \<longlongrightarrow> b) (finite_subsets_at_top B)"
    using has_setprod_def by auto
  from assms(2) have limA: "(prod f \<longlongrightarrow> a) (finite_subsets_at_top A)"
    using has_setprod_def by blast
  have "((\<lambda>F. prod f (F\<inter>A)) \<longlongrightarrow> a) (finite_subsets_at_top B)"
  proof (subst asm_rl [of "(\<lambda>F. prod f (F\<inter>A)) = prod f \<circ> (\<lambda>F. F\<inter>A)"])
    show "(\<lambda>F. prod f (F \<inter> A)) = prod f \<circ> (\<lambda>F. F \<inter> A)"
      unfolding o_def by auto
    show "((prod f \<circ> (\<lambda>F. F \<inter> A)) \<longlongrightarrow> a) (finite_subsets_at_top B)"
      unfolding o_def 
      using tendsto_compose_filtermap finite_subsets2 limA tendsto_mono
        \<open>(\<lambda>F. prod f (F \<inter> A)) = prod f \<circ> (\<lambda>F. F \<inter> A)\<close> by fastforce
  qed

  with limB have "((\<lambda>F. prod f F / prod f (F\<inter>A)) \<longlongrightarrow> b / a) (finite_subsets_at_top B)"
    by (intro tendsto_divide) auto
  have "prod f X / prod f (X \<inter> A) = prod f (X - A)" 
    if "finite X" and "X \<subseteq> B" for X :: "'b set"
  proof (subst prod.Int_Diff[of _ _ A])
    have "prod f (X \<inter> A) \<noteq> 0"
      using that by (auto simp: nonzero)
    thus "prod f (X \<inter> A) * prod f (X - A) / prod f (X \<inter> A) = prod f (X - A)"
      by simp
  qed fact+
  hence "\<forall>\<^sub>F x in finite_subsets_at_top B. prod f x / prod f (x \<inter> A) = prod f (x - A)"
    by (rule eventually_finite_subsets_at_top_weakI)  
  hence "((\<lambda>F. prod f (F-A)) \<longlongrightarrow> b / a) (finite_subsets_at_top B)"
    using tendsto_cong [THEN iffD1 , rotated]
      \<open>((\<lambda>F. prod f F / prod f (F \<inter> A)) \<longlongrightarrow> b / a) (finite_subsets_at_top B)\<close> by fastforce
  hence "(prod f \<longlongrightarrow> b / a) (filtermap (\<lambda>F. F-A) (finite_subsets_at_top B))"
    by (subst tendsto_compose_filtermap[symmetric], simp add: o_def)
  thus ?thesis
    using finite_subsets1 has_setprod_def tendsto_mono by blast
qed

lemma multipliable_on_finite[simp]:
  assumes "finite F"
  shows "f multipliable_on F"
  using assms multipliable_on_def has_setprod_finite by blast

lemma infprod_finite[simp]:
  assumes "finite F"
  shows "infprod f F = prod f F"
  using assms by (simp add: has_setprod_finite infprodI)

lemma has_setprod_finite_approximation:
  fixes f :: "'a \<Rightarrow> 'b::{semidom,topological_semigroup_mult,metric_space}"
  assumes "(f has_setprod x) A" and "\<epsilon> > 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> A \<and> dist (prod f F) x \<le> \<epsilon>"
proof -
  have "(prod f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    by (simp add: assms(1) has_setprodD)
  hence *: "\<forall>\<^sub>F F in (finite_subsets_at_top A). dist (prod f F) x < \<epsilon>"
    using assms(2) by (rule tendstoD)
  thus ?thesis
    unfolding eventually_finite_subsets_at_top by fastforce
qed

lemma infprod_finite_approximation:
  fixes f :: "'a \<Rightarrow> 'b::{semidom,topological_semigroup_mult,metric_space}"
  assumes "f multipliable_on A" and "\<epsilon> > 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> A \<and> dist (prod f F) (infprod f A) \<le> \<epsilon>"
proof -
  from assms have "(f has_setprod (infprod f A)) A"
    by (simp add: multipliable_iff_has_setprod_infprod)
  from this and \<open>\<epsilon> > 0\<close> show ?thesis
    by (rule has_setprod_finite_approximation)
qed

theorem abs_convergent_prod_imp_convergent_prod:
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_div_algebra,complete_space,comm_ring_1}"
  assumes "abs_convergent_prod f"
  shows   "convergent_prod f"
proof -
  from assms have "eventually (\<lambda>n. f n \<noteq> 0) sequentially"
    by (rule abs_convergent_prod_imp_ev_nonzero)
  then obtain N where N: "f n \<noteq> 0" if "n \<ge> N" for n 
    by (auto simp: eventually_at_top_linorder)
  let ?P = "\<lambda>n. \<Prod>i\<le>n. f (i + N)" and ?Q = "\<lambda>n. \<Prod>i\<le>n. 1 + norm (f (i + N) - 1)"

  have "Cauchy ?P"
  proof (rule CauchyI', goal_cases)
    case (1 \<epsilon>)
    from assms have "abs_convergent_prod (\<lambda>n. f (n + N))"
      by (rule abs_convergent_prod_ignore_initial_segment)
    hence "Cauchy ?Q"
      unfolding abs_convergent_prod_def
      by (intro convergent_Cauchy convergent_prod_imp_convergent)
    from CauchyD[OF this 1] obtain M where M: "norm (?Q m - ?Q n) < \<epsilon>" if "m \<ge> M" "n \<ge> M" for m n
      by blast
    show ?case
    proof (rule exI[of _ M], safe, goal_cases)
      case (1 m n)
      have "dist (?P m) (?P n) = norm (?P n - ?P m)"
        by (simp add: dist_norm norm_minus_commute)
      also from 1 have "{..n} = {..m} \<union> {m<..n}" by auto
      hence "norm (?P n - ?P m) = norm (?P m * (\<Prod>k\<in>{m<..n}. f (k + N)) - ?P m)"
        by (subst prod.union_disjoint [symmetric]) (auto simp: algebra_simps)
      also have "\<dots> = norm (?P m * ((\<Prod>k\<in>{m<..n}. f (k + N)) - 1))"
        by (simp add: algebra_simps)
      also have "\<dots> = (\<Prod>k\<le>m. norm (f (k + N))) * norm ((\<Prod>k\<in>{m<..n}. f (k + N)) - 1)"
        by (simp add: norm_mult prod_norm)
      also have "\<dots> \<le> ?Q m * ((\<Prod>k\<in>{m<..n}. 1 + norm (f (k + N) - 1)) - 1)"
        using norm_prod_minus1_le_prod_minus1[of "\<lambda>k. f (k + N) - 1" "{m<..n}"]
              norm_triangle_ineq[of 1 "f k - 1" for k]
        by (intro mult_mono prod_mono ballI conjI norm_prod_minus1_le_prod_minus1 prod_nonneg) auto
      also have "\<dots> = ?Q m * (\<Prod>k\<in>{m<..n}. 1 + norm (f (k + N) - 1)) - ?Q m"
        by (simp add: algebra_simps)
      also have "?Q m * (\<Prod>k\<in>{m<..n}. 1 + norm (f (k + N) - 1)) = 
                   (\<Prod>k\<in>{..m}\<union>{m<..n}. 1 + norm (f (k + N) - 1))"
        by (rule prod.union_disjoint [symmetric]) auto
      also from 1 have "{..m}\<union>{m<..n} = {..n}" by auto
      also have "?Q n - ?Q m \<le> norm (?Q n - ?Q m)" by simp
      also from 1 have "\<dots> < \<epsilon>" by (intro M) auto
      finally show ?case .
    qed
  qed
  hence conv: "convergent ?P" by (rule Cauchy_convergent)
  then obtain L where L: "?P \<longlonglongrightarrow> L"
    by (auto simp: convergent_def)

  have "L \<noteq> 0"
  proof
    assume [simp]: "L = 0"
    from tendsto_norm[OF L] have limit: "(\<lambda>n. \<Prod>k\<le>n. norm (f (k + N))) \<longlonglongrightarrow> 0" 
      by (simp add: prod_norm)

    from assms have "(\<lambda>n. f (n + N)) \<longlonglongrightarrow> 1"
      by (intro abs_convergent_prod_imp_LIMSEQ abs_convergent_prod_ignore_initial_segment)
    hence "eventually (\<lambda>n. norm (f (n + N) - 1) < 1) sequentially"
      by (auto simp: tendsto_iff dist_norm)
    then obtain M0 where M0: "norm (f (n + N) - 1) < 1" if "n \<ge> M0" for n
      by (auto simp: eventually_at_top_linorder)

    {
      fix M assume M: "M \<ge> M0"
      with M0 have M: "norm (f (n + N) - 1) < 1" if "n \<ge> M" for n using that by simp

      have "(\<lambda>n. \<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1)) \<longlonglongrightarrow> 0"
      proof (rule tendsto_sandwich)
        show "eventually (\<lambda>n. (\<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1)) \<ge> 0) sequentially"
          using M by (intro always_eventually prod_nonneg allI ballI) (auto intro: less_imp_le)
        have "norm (1::'a) - norm (f (i + M + N) - 1) \<le> norm (f (i + M + N))" for i
          using norm_triangle_ineq3[of "f (i + M + N)" 1] by simp
        thus "eventually (\<lambda>n. (\<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1)) \<le> (\<Prod>k\<le>n. norm (f (k+M+N)))) at_top"
          using M by (intro always_eventually allI prod_mono ballI conjI) (auto intro: less_imp_le)
        
        define C where "C = (\<Prod>k<M. norm (f (k + N)))"
        from N have [simp]: "C \<noteq> 0" by (auto simp: C_def)
        from L have "(\<lambda>n. norm (\<Prod>k\<le>n+M. f (k + N))) \<longlonglongrightarrow> 0"
          by (intro LIMSEQ_ignore_initial_segment) (simp add: tendsto_norm_zero_iff)
        also have "(\<lambda>n. norm (\<Prod>k\<le>n+M. f (k + N))) = (\<lambda>n. C * (\<Prod>k\<le>n. norm (f (k + M + N))))"
        proof (rule ext, goal_cases)
          case (1 n)
          have "{..n+M} = {..<M} \<union> {M..n+M}" by auto
          also have "norm (\<Prod>k\<in>\<dots>. f (k + N)) = C * norm (\<Prod>k=M..n+M. f (k + N))"
            unfolding C_def by (subst prod.union_disjoint) (auto simp: norm_mult prod_norm)
          also have "(\<Prod>k=M..n+M. f (k + N)) = (\<Prod>k\<le>n. f (k + N + M))"
            by (intro prod.reindex_bij_witness[of _ "\<lambda>i. i + M" "\<lambda>i. i - M"]) auto
          finally show ?case by (simp add: add_ac prod_norm)
        qed
        finally have "(\<lambda>n. C * (\<Prod>k\<le>n. norm (f (k + M + N))) / C) \<longlonglongrightarrow> 0 / C"
          by (intro tendsto_divide tendsto_const) auto
        thus "(\<lambda>n. \<Prod>k\<le>n. norm (f (k + M + N))) \<longlonglongrightarrow> 0" by simp
      qed simp_all

      have "1 - (\<Sum>i. norm (f (i + M + N) - 1)) \<le> 0"
      proof (rule tendsto_le)
        show "eventually (\<lambda>n. 1 - (\<Sum>k\<le>n. norm (f (k+M+N) - 1)) \<le> 
                                (\<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1))) at_top"
          using M by (intro always_eventually allI Weierstrass_prod_ineq) (auto intro: less_imp_le)
        show "(\<lambda>n. \<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1)) \<longlonglongrightarrow> 0" by fact
        show "(\<lambda>n. 1 - (\<Sum>k\<le>n. norm (f (k + M + N) - 1)))
                  \<longlonglongrightarrow> 1 - (\<Sum>i. norm (f (i + M + N) - 1))"
          by (intro tendsto_intros summable_LIMSEQ' summable_ignore_initial_segment 
                abs_convergent_prod_imp_summable assms)
      qed simp_all
      hence "(\<Sum>i. norm (f (i + M + N) - 1)) \<ge> 1" by simp
      also have "\<dots> + (\<Sum>i<M. norm (f (i + N) - 1)) = (\<Sum>i. norm (f (i + N) - 1))"
        by (intro suminf_split_initial_segment [symmetric] summable_ignore_initial_segment
              abs_convergent_prod_imp_summable assms)
      finally have "1 + (\<Sum>i<M. norm (f (i + N) - 1)) \<le> (\<Sum>i. norm (f (i + N) - 1))" by simp
    } note * = this

    have "1 + (\<Sum>i. norm (f (i + N) - 1)) \<le> (\<Sum>i. norm (f (i + N) - 1))"
    proof (rule tendsto_le)
      show "(\<lambda>M. 1 + (\<Sum>i<M. norm (f (i + N) - 1))) \<longlonglongrightarrow> 1 + (\<Sum>i. norm (f (i + N) - 1))"
        by (intro tendsto_intros summable_LIMSEQ summable_ignore_initial_segment 
                abs_convergent_prod_imp_summable assms)
      show "eventually (\<lambda>M. 1 + (\<Sum>i<M. norm (f (i + N) - 1)) \<le> (\<Sum>i. norm (f (i + N) - 1))) at_top"
        using eventually_ge_at_top[of M0] by eventually_elim (use * in auto)
    qed simp_all
    thus False by simp
  qed
  with L show ?thesis by (auto simp: prod_defs)
qed

lemma abs_multipliable_multipliable:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {banach, real_normed_div_algebra, semidom}\<close>
  assumes \<open>f abs_multipliable_on A\<close>
  shows \<open>f multipliable_on A\<close>
  sorry
(*
proof -
  from assms obtain L where lim: \<open>(prod (\<lambda>x. 1 + norm (f x - 1)) \<longlongrightarrow> L) (finite_subsets_at_top A)\<close>
    unfolding has_setprod_def abs_multipliable_on_def multipliable_on_def by blast
  then have *: \<open>cauchy_filter (filtermap (prod (\<lambda>x. 1 + norm (f x - 1))) (finite_subsets_at_top A))\<close>
    by (auto intro!: nhds_imp_cauchy_filter simp: filterlim_def)
  have \<open>\<exists>P. eventually P (finite_subsets_at_top A) \<and>
              (\<forall>F F'. P F \<and> P F' \<longrightarrow> dist (prod f F) (prod f F') < e)\<close> if \<open>e>0\<close> for e
  proof -
    define d P where \<open>d = e/4\<close> and \<open>P F \<longleftrightarrow> finite F \<and> F \<subseteq> A \<and> dist (prod (\<lambda>x. 1 + norm (f x - 1)) F) L < d\<close> for F
    then have \<open>d > 0\<close>
      by (simp add: d_def that)
    have ev_P: \<open>eventually P (finite_subsets_at_top A)\<close>
      using lim
      by (auto simp add: P_def[abs_def] \<open>0 < d\<close> eventually_conj_iff eventually_finite_subsets_at_top_weakI tendsto_iff)
    
    moreover have \<open>dist (prod f F1) (prod f F2) < e\<close> if \<open>P F1\<close> and \<open>P F2\<close> for F1 F2
    proof -
      from ev_P
      obtain F' where \<open>finite F'\<close> and \<open>F' \<subseteq> A\<close> and P_sup_F': \<open>finite F \<and> F \<supseteq> F' \<and> F \<subseteq> A \<Longrightarrow> P F\<close> for F
        by atomize_elim (simp add: eventually_finite_subsets_at_top)
      define F where \<open>F = F' \<union> F1 \<union> F2\<close>
      have \<open>finite F\<close> and \<open>F \<subseteq> A\<close>
        using F_def P_def[abs_def] that \<open>finite F'\<close> \<open>F' \<subseteq> A\<close> by auto
      have dist_F: \<open>dist (prod (\<lambda>x. 1 + norm (f x - 1)) F) L < d\<close>
        by (metis F_def \<open>F \<subseteq> A\<close> P_def P_sup_F' \<open>finite F\<close> le_supE order_refl)

      have dist_F_subset: \<open>dist (prod f F) (prod f F') < 2*d\<close> if F': \<open>F' \<subseteq> F\<close> \<open>P F'\<close> for F'
      proof -
        have \<open>dist (prod f F) (prod f F') = norm (prod f (F-F'))\<close>
          unfolding dist_norm using \<open>finite F\<close> F' by (subst sum_diff) auto
        also have \<open>\<dots> \<le> norm (\<Prod>x\<in>F-F'. norm (f x))\<close>
          by (rule order.trans[OF sum_norm_le[OF order.refl]]) auto
        also have \<open>\<dots> = dist (\<Prod>x\<in>F. norm (f x)) (\<Prod>x\<in>F'. norm (f x))\<close>
          unfolding dist_norm using \<open>finite F\<close> F' by (subst sum_diff) auto
        also have \<open>\<dots> < 2 * d\<close>
          using dist_F F' unfolding P_def dist_norm real_norm_def by linarith
        finally show \<open>dist (prod f F) (prod f F') < 2*d\<close> .
      qed

      have \<open>dist (prod f F1) (prod f F2) \<le> dist (prod f F) (prod f F1) + dist (prod f F) (prod f F2)\<close>
        by (rule dist_triangle3)
      also have \<open>\<dots> < 2 * d + 2 * d\<close>
        by (intro add_strict_mono dist_F_subset that) (auto simp: F_def)
      also have \<open>\<dots> \<le> e\<close>
        by (auto simp: d_def)
      finally show \<open>dist (prod f F1) (prod f F2) < e\<close> .
    qed
    then show ?thesis
      using ev_P by blast
  qed
  then have \<open>cauchy_filter (filtermap (prod f) (finite_subsets_at_top A))\<close>
    by (simp add: cauchy_filter_metric_filtermap)
  moreover have "complete (UNIV::'b set)"
    by (meson Cauchy_convergent UNIV_I complete_def convergent_def)
  ultimately obtain L' where \<open>(prod f \<longlongrightarrow> L') (finite_subsets_at_top A)\<close>
    using complete_uniform[where S=UNIV] by (force simp add: filterlim_def)
  then show ?thesis
    using multipliable_on_def has_setprod_def by blast
qed
*)

lemma infprod_tendsto:
  assumes \<open>f multipliable_on S\<close>
  shows \<open>((\<lambda>F. prod f F) \<longlongrightarrow> infprod f S) (finite_subsets_at_top S)\<close>
  using assms has_setprod_infprod by (simp add: has_setprodD)

lemma has_setprod_1: 
  assumes \<open>\<And>x. x \<in> M \<Longrightarrow> f x = 1\<close>
  shows \<open>(f has_setprod 1) M\<close>
proof -
  have "(f has_setprod 1) M \<longleftrightarrow> ((\<lambda>_ :: 'a. 1 :: 'b) has_setprod 1) {}"
    by (intro has_setprod_cong_neutral) (use assms in auto)
  thus ?thesis
    by simp
qed

lemma multipliable_on_1:
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 1\<close>
  shows \<open>f multipliable_on M\<close>
  using assms multipliable_on_def has_setprod_1 by blast

lemma infprod_1:
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 1\<close>
  shows \<open>infprod f M = 1\<close>
  using assms by (simp add: has_setprod_1 infprodI)

lemma infprod_0_simp[simp]: \<open>infprod (\<lambda>_. 1) M = 1\<close>
  by (simp_all add: infprod_1)

lemma multipliable_on_0_simp[simp]: \<open>(\<lambda>_. 1) multipliable_on M\<close>
  by (simp_all add: multipliable_on_1)

lemma has_setprod_0_simp[simp]: \<open>((\<lambda>_. 1) has_setprod 1) M\<close>
  by (simp_all add: has_setprod_1)

lemma multipliable_on_mult:
  fixes f g :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, field, t2_space}"
  assumes \<open>f multipliable_on A\<close>
  assumes \<open>g multipliable_on A\<close>
  shows \<open>(\<lambda>x. f x * g x) multipliable_on A\<close>
  by (metis (full_types) assms multipliable_on_def has_setprod_mult)

lemma infprod_mult:
  fixes f g :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, field, t2_space}"
  assumes \<open>f multipliable_on A\<close>
  assumes \<open>g multipliable_on A\<close>
  shows \<open>infprod (\<lambda>x. f x * g x) A = infprod f A * infprod g A\<close>
proof -
  have \<open>((\<lambda>x. f x * g x) has_setprod (infprod f A * infprod g A)) A\<close>
    by (simp add: assms has_setprod_mult)
  then show ?thesis
    using infprodI by blast
qed

lemma multipliable_on_Un_disjoint:
  fixes f g :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, field, t2_space}"
  assumes "f multipliable_on A"
  assumes "f multipliable_on B"
  assumes disj: "A \<inter> B = {}"
  shows \<open>f multipliable_on (A \<union> B)\<close>
  by (meson assms disj multipliable_on_def has_setprod_Un_disjoint)

lemma infprod_Un_disjoint:
  fixes f g :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, field, t2_space}"
  assumes "f multipliable_on A"
  assumes "f multipliable_on B"
  assumes disj: "A \<inter> B = {}"
  shows \<open>infprod f (A \<union> B) = infprod f A * infprod f B\<close>
  by (intro infprodI has_setprod_Un_disjoint has_setprod_infprod assms)  

lemma abs_convergent_prod_imp_setprod:
  fixes f :: "nat \<Rightarrow> 'b :: {topological_semigroup_mult, field, real_normed_vector}"
  assumes "abs_convergent_prod f" and "f has_prod P"
  shows   "(f has_setprod P) (UNIV :: nat set)"
  sorry

lemma abs_convergent_prod_imp_multipliable_on:
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_field,complete_space,comm_ring_1}"
  assumes "abs_convergent_prod f"
  shows   "f multipliable_on UNIV"
proof -
  from assms have "convergent_prod f"
    by (rule abs_convergent_prod_imp_convergent_prod)
  thus ?thesis
    using abs_convergent_prod_imp_setprod[OF assms] multipliable_on_def by blast
qed

lemma abs_multipliable_on_iff_summable_on:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra_1}"
  shows "f abs_multipliable_on A \<longleftrightarrow> (\<lambda>n. norm (f x - 1)) summable_on A"
  using abs_convergent_prod_conv_summable sorry

lemma multipliable_on_subset_aux:
  fixes A B and f :: \<open>'a \<Rightarrow> 'b::{uniform_space, field, t2_space, topological_semigroup_mult}\<close>
  assumes \<open>complete (UNIV :: 'b set)\<close>
  assumes times_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'b,y). x*y)\<close>
  assumes \<open>f multipliable_on A\<close>
  assumes \<open>B \<subseteq> A\<close>
  shows \<open>f multipliable_on B\<close>
(*
proof -
  let ?filter_fB = \<open>filtermap (prod f) (finite_subsets_at_top B)\<close>
  from \<open>f multipliable_on A\<close>
  obtain S where \<open>(prod f \<longlongrightarrow> S) (finite_subsets_at_top A)\<close> (is \<open>(prod f \<longlongrightarrow> S) ?filter_A\<close>)
    using multipliable_on_def has_setprod_def by blast
  then have cauchy_fA: \<open>cauchy_filter (filtermap (prod f) (finite_subsets_at_top A))\<close> (is \<open>cauchy_filter ?filter_fA\<close>)
    by (auto intro!: nhds_imp_cauchy_filter simp: filterlim_def)

  have \<open>cauchy_filter (filtermap (prod f) (finite_subsets_at_top B))\<close>
  proof (unfold cauchy_filter_def, rule filter_leI)
    fix E :: \<open>('b\<times>'b) \<Rightarrow> bool\<close> assume \<open>eventually E uniformity\<close>
    then obtain E' where \<open>eventually E' uniformity\<close> and E'E'E: \<open>E' (x, y) \<longrightarrow> E' (y, z) \<longrightarrow> E (x, z)\<close> for x y z
      using uniformity_trans by blast
    obtain D where \<open>eventually D uniformity\<close> and DE: \<open>D (x, y) \<Longrightarrow> E' (x*c, y*c)\<close> for x y c
      using times_cont \<open>eventually E' uniformity\<close>
      unfolding uniformly_continuous_on_uniformity filterlim_def le_filter_def uniformity_prod_def
      by (auto simp: case_prod_beta eventually_filtermap eventually_prod_same uniformity_refl)
    have DE': "E' (x, y)" if "D (x * c, y * c)" "c \<noteq> 0" for x y c
      using DE[of "x * c" "y * c" "inverse c"] that by (simp add: field_simps)

    from \<open>eventually D uniformity\<close> and cauchy_fA have \<open>eventually D (?filter_fA \<times>\<^sub>F ?filter_fA)\<close>
      unfolding cauchy_filter_def le_filter_def by simp
    then obtain P1 P2
      where ev_P1: \<open>eventually (\<lambda>F. P1 (prod f F)) ?filter_A\<close> 
        and ev_P2: \<open>eventually (\<lambda>F. P2 (prod f F)) ?filter_A\<close>
        and P1P2E: \<open>P1 x \<Longrightarrow> P2 y \<Longrightarrow> D (x, y)\<close> for x y
      unfolding eventually_prod_filter eventually_filtermap
      by auto
    from ev_P1 obtain F1 where F1: \<open>finite F1\<close> \<open>F1 \<subseteq> A\<close> \<open>\<And>F. F\<supseteq>F1 \<Longrightarrow> finite F \<Longrightarrow> F\<subseteq>A \<Longrightarrow> P1 (prod f F)\<close>
      by (metis eventually_finite_subsets_at_top)
    from ev_P2 obtain F2 where F2: \<open>finite F2\<close> \<open>F2 \<subseteq> A\<close> \<open>\<And>F. F\<supseteq>F2 \<Longrightarrow> finite F \<Longrightarrow> F\<subseteq>A \<Longrightarrow> P2 (prod f F)\<close>
      by (metis eventually_finite_subsets_at_top)
    define F0 F0A F0B where \<open>F0 \<equiv> F1 \<union> F2\<close> and \<open>F0A \<equiv> F0 - B\<close> and \<open>F0B \<equiv> F0 \<inter> B\<close>
    have [simp]: \<open>finite F0\<close>  \<open>F0 \<subseteq> A\<close>
      using \<open>F1 \<subseteq> A\<close> \<open>F2 \<subseteq> A\<close> \<open>finite F1\<close> \<open>finite F2\<close> unfolding F0_def by blast+
 
    have *: "E' (prod f F1', prod f F2')"
      if "F1'\<supseteq>F0B" "F2'\<supseteq>F0B" "finite F1'" "finite F2'" "F1'\<subseteq>B" "F2'\<subseteq>B" for F1' F2'
    proof (intro DE'[where c = "prod f F0A"] P1P2E)
      have "P1 (prod f (F1' \<union> F0A))"
        using that assms F1(1,2) F2(1,2) by (intro F1) (auto simp: F0A_def F0B_def F0_def)
      thus "P1 (prod f F1' * prod f F0A)"
        by (subst (asm) prod.union_disjoint) (use that in \<open>auto simp: F0A_def\<close>)
    next
      have "P2 (prod f (F2' \<union> F0A))"
        using that assms F1(1,2) F2(1,2) by (intro F2) (auto simp: F0A_def F0B_def F0_def)
      thus "P2 (prod f F2' * prod f F0A)"
        by (subst (asm) prod.union_disjoint) (use that in \<open>auto simp: F0A_def\<close>)   
    next
      show "prod f F0A \<noteq> 0"
        sorry
    qed

    have "eventually (\<lambda>x. E' (x, prod f F0B)) (filtermap (prod f) (finite_subsets_at_top B))"
     and "eventually (\<lambda>x. E' (prod f F0B, x)) (filtermap (prod f) (finite_subsets_at_top B))"
        unfolding eventually_filtermap eventually_finite_subsets_at_top
        by (rule exI[of _ F0B]; use * in \<open>force simp: F0B_def\<close>)+
      then 
    show \<open>eventually E (?filter_fB \<times>\<^sub>F ?filter_fB)\<close>
      unfolding eventually_prod_filter
      using E'E'E by blast
  qed

  then obtain x where \<open>?filter_fB \<le> nhds x\<close>
    using cauchy_filter_complete_converges[of ?filter_fB UNIV] \<open>complete (UNIV :: _)\<close>
    by (auto simp: filtermap_bot_iff)
  then have \<open>(prod f \<longlongrightarrow> x) (finite_subsets_at_top B)\<close>
    by (auto simp: filterlim_def)
  then show ?thesis
    by (auto simp: multipliable_on_def has_setprod_def)
qed
*)
  sorry

lemma multipliable_on_subset_banach:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach, field, topological_semigroup_mult}\<close>
  assumes \<open>f multipliable_on A\<close>
  assumes \<open>B \<subseteq> A\<close>
  shows \<open>f multipliable_on B\<close>
  sorry

lemma has_prod_Diff:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach, field, topological_semigroup_mult}\<close>
  assumes "(f has_setprod PA) A" "(f has_setprod PB) B" "PA \<noteq> 0" "A \<subseteq> B"
  shows   "(f has_setprod (PB / PA)) (A - B)"
  sorry




lemma has_setprod_empty[simp]: \<open>(f has_setprod 1) {}\<close>
  by (meson ex_in_conv has_setprod_1)

lemma multipliable_on_empty[simp]: \<open>f multipliable_on {}\<close>
  by auto

lemma infprod_empty[simp]: \<open>infprod f {} = 1\<close>
  by simp

lemma prod_has_setprod:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach, field, topological_semigroup_mult}\<close>
  assumes \<open>finite A\<close>
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> (f has_setprod (s a)) (B a)\<close>
  assumes \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>(f has_setprod (prod s A)) (\<Union>a\<in>A. B a)\<close>
  using assms 
proof (induction)
  case empty
  then show ?case 
    by simp
next
  case (insert x A)
  have \<open>(f has_setprod (s x)) (B x)\<close>
    by (simp add: insert.prems)
  moreover have IH: \<open>(f has_setprod (prod s A)) (\<Union>a\<in>A. B a)\<close>
    using insert by simp
  ultimately have \<open>(f has_setprod (s x * prod s A)) (B x \<union> (\<Union>a\<in>A. B a))\<close>
    using insert by (intro has_setprod_Un_disjoint) auto
  then show ?case
    using insert.hyps by auto
qed


lemma multipliable_on_finite_union_disjoint:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach, field, topological_semigroup_mult}\<close>
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> f multipliable_on (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>f multipliable_on (\<Union>a\<in>A. B a)\<close>
  using prod_has_setprod [of A f B] assms unfolding multipliable_on_def by metis

lemma prod_infprod:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach, field, topological_semigroup_mult}\<close>
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> f multipliable_on (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>prod (\<lambda>a. infprod f (B a)) A = infprod f (\<Union>a\<in>A. B a)\<close>
  by (metis (no_types, lifting) assms has_setprod_infprod infprodI prod_has_setprod)

lemma has_setprod_comm_multiplicative_general: 
  fixes f :: \<open>'b::{banach, field, topological_semigroup_mult} \<Rightarrow> 'c::{banach, field, topological_semigroup_mult}\<close>
  assumes f_sum: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> prod (f \<circ> g) F = f (prod g F)\<close>
  assumes cont: \<open>f \<midarrow>x\<rightarrow> f x\<close>
  assumes infprod: \<open>(g has_setprod x) S\<close>
  shows \<open>((f \<circ> g) has_setprod (f x)) S\<close> 
  sorry (*
proof -
  have \<open>(prod g \<longlongrightarrow> x) (finite_subsets_at_top S)\<close>
    using infprod has_setprod_def by blast
  then have \<open>((f \<circ> prod g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
    by (meson cont filterlim_def tendsto_at_iff_tendsto_nhds tendsto_compose_filtermap tendsto_mono)
  then have \<open>(prod (f \<circ> g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
    using tendsto_cong f_sum
    by (simp add: Lim_transform_eventually eventually_finite_subsets_at_top_weakI)
  then show \<open>((f \<circ> g) has_setprod (f x)) S\<close>
    using has_setprod_def by blast 
qed 

lemma multipliable_on_comm_multiplicative_general:
  fixes f :: \<open>'b :: {comm_monoid_mult,topological_space} \<Rightarrow> 'c :: {comm_monoid_mult,topological_space}\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> prod (f \<circ> g) F = f (prod g F)\<close>
    \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes \<open>\<And>x. (g has_setprod x) S \<Longrightarrow> f \<midarrow>x\<rightarrow> f x\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes \<open>g multipliable_on S\<close>
  shows \<open>(f \<circ> g) multipliable_on S\<close>
  by (meson assms multipliable_on_def has_setprod_comm_multiplicative_general has_setprod_def infprod_tendsto)

lemma infprod_comm_additive_general:
  fixes f :: \<open>'b :: {comm_monoid_mult,t2_space} \<Rightarrow> 'c :: {comm_monoid_mult,t2_space}\<close>
  assumes f_sum: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> prod (f \<circ> g) F = f (prod g F)\<close>
      \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes \<open>isCont f (infprod g S)\<close>
  assumes \<open>g multipliable_on S\<close>
  shows \<open>infprod (f \<circ> g) S = f (infprod g S)\<close>
  using assms
  by (intro infprodI has_setprod_comm_multiplicative_general has_setprod_infprod) (auto simp: isCont_def)

*)

lemma has_setprod_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>(g has_setprod P) (h ` A) \<longleftrightarrow> ((g \<circ> h) has_setprod P) A\<close>
proof -
  have \<open>(g has_setprod P) (h ` A) \<longleftrightarrow> (prod g \<longlongrightarrow> P) (finite_subsets_at_top (h ` A))\<close>
    by (simp add: has_setprod_def)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>F. prod g (h ` F)) \<longlongrightarrow> P) (finite_subsets_at_top A)\<close>
    by (metis assms filterlim_filtermap filtermap_image_finite_subsets_at_top)
  also have \<open>\<dots> \<longleftrightarrow> (prod (g \<circ> h) \<longlongrightarrow> P) (finite_subsets_at_top A)\<close>
  proof (intro tendsto_cong eventually_finite_subsets_at_top_weakI prod.reindex)
    show "\<And>X. \<lbrakk>finite X; X \<subseteq> A\<rbrakk> \<Longrightarrow> inj_on h X"
      using assms subset_inj_on by blast
  qed
  also have \<open>\<dots> \<longleftrightarrow> ((g \<circ> h) has_setprod P) A\<close>
    by (simp add: has_setprod_def)
  finally show ?thesis .
qed

lemma multipliable_on_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>g multipliable_on (h ` A) \<longleftrightarrow> (g \<circ> h) multipliable_on A\<close>
  by (simp add: assms multipliable_on_def has_setprod_reindex)

lemma infprod_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>infprod g (h ` A) = infprod (g \<circ> h) A\<close>
  by (metis assms has_setprod_infprod has_setprod_reindex infprodI infprod_def)

lemma multipliable_on_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "(\<lambda>x. f (g x)) multipliable_on A \<longleftrightarrow> f multipliable_on B"
  by (smt (verit) assms bij_betw_def o_apply multipliable_on_cong multipliable_on_reindex) 

lemma infprod_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "infprod (\<lambda>x. f (g x)) A = infprod f B"
  by (metis (mono_tags, lifting) assms bij_betw_def infprod_cong infprod_reindex o_def)

lemma prod_uniformity:
  assumes times_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'b::{uniform_space,comm_monoid_mult},y). x*y)\<close>
  assumes EE: \<open>eventually E uniformity\<close>
  obtains D where \<open>eventually D uniformity\<close> 
    and \<open>\<And>M::'a set. \<And>f f' :: 'a \<Rightarrow> 'b. card M \<le> n \<and> (\<forall>m\<in>M. D (f m, f' m)) \<Longrightarrow> E (prod f M, prod f' M)\<close>
proof (atomize_elim, insert EE, induction n arbitrary: E rule:nat_induct)
  case 0
  then show ?case
    by (metis card_eq_0_iff equals0D le_zero_eq prod.infinite prod.not_neutral_contains_not_neutral uniformity_refl)
next
  case (Suc n)
  from times_cont[unfolded uniformly_continuous_on_uniformity filterlim_def le_filter_def, rule_format, OF Suc.prems]
  obtain D1 D2 where \<open>eventually D1 uniformity\<close> and \<open>eventually D2 uniformity\<close> 
    and D1D2E: \<open>D1 (x, y) \<Longrightarrow> D2 (x', y') \<Longrightarrow> E (x * x', y * y')\<close> for x y x' y'
    apply atomize_elim
    by (auto simp: eventually_prod_filter case_prod_beta uniformity_prod_def eventually_filtermap)

  from Suc.IH[OF \<open>eventually D2 uniformity\<close>]
  obtain D3 where \<open>eventually D3 uniformity\<close> and D3: \<open>card M \<le> n \<Longrightarrow> (\<forall>m\<in>M. D3 (f m, f' m)) \<Longrightarrow> D2 (prod f M, prod f' M)\<close> 
    for M :: \<open>'a set\<close> and f f'
    by metis

  define D where \<open>D x \<equiv> D1 x \<and> D3 x\<close> for x
  have \<open>eventually D uniformity\<close>
    using D_def \<open>eventually D1 uniformity\<close> \<open>eventually D3 uniformity\<close> eventually_elim2 by blast

  have \<open>E (prod f M, prod f' M)\<close> 
    if \<open>card M \<le> Suc n\<close> and DM: \<open>\<forall>m\<in>M. D (f m, f' m)\<close>
    for M :: \<open>'a set\<close> and f f'
  proof (cases \<open>card M = 0\<close>)
    case True
    then show ?thesis
      by (metis Suc.prems card_eq_0_iff prod.empty prod.infinite uniformity_refl) 
  next
    case False
    with \<open>card M \<le> Suc n\<close> obtain N x where \<open>card N \<le> n\<close> and \<open>x \<notin> N\<close> and \<open>M = insert x N\<close>
      by (metis card_Suc_eq less_Suc_eq_0_disj less_Suc_eq_le)

    from DM have \<open>\<And>m. m\<in>N \<Longrightarrow> D (f m, f' m)\<close>
      using \<open>M = insert x N\<close> by blast
    with D3[OF \<open>card N \<le> n\<close>]
    have D2_N: \<open>D2 (prod f N, prod f' N)\<close>
      using D_def by blast

    from DM 
    have \<open>D (f x, f' x)\<close>
      using \<open>M = insert x N\<close> by blast
    then have \<open>D1 (f x, f' x)\<close>
      by (simp add: D_def)

    with D2_N
    have \<open>E (f x * prod f N, f' x * prod f' N)\<close>
      using D1D2E by presburger

    then show \<open>E (prod f M, prod f' M)\<close>
      by (metis False \<open>M = insert x N\<close> \<open>x \<notin> N\<close> card.infinite finite_insert prod.insert)
  qed
  with \<open>eventually D uniformity\<close> show ?case 
    by auto
qed

lemma has_setprod_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{field,uniform_space,topological_semigroup_mult,t2_space}\<close>
  assumes times_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x*y)\<close>
  assumes multipliableAB: "(f has_setprod a) (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod b x) (B x)\<close>
  shows "(b has_setprod a) A"
proof -
  define F FB FA where \<open>F = finite_subsets_at_top (Sigma A B)\<close> and \<open>FB x = finite_subsets_at_top (B x)\<close>
    and \<open>FA = finite_subsets_at_top A\<close> for x

  from multipliableB
  have sum_b: \<open>(prod (\<lambda>y. f (x, y)) \<longlongrightarrow> b x) (FB x)\<close> if \<open>x \<in> A\<close> for x
    using FB_def[abs_def] has_setprod_def that by auto
  from multipliableAB
  have sum_S: \<open>(prod f \<longlongrightarrow> a) F\<close>
    using F_def has_setprod_def by blast

  have finite_proj: \<open>finite {b| b. (a,b) \<in> H}\<close> if \<open>finite H\<close> for H :: \<open>('a\<times>'b) set\<close> and a
    by (metis (no_types, lifting) finite_imageI finite_subset image_eqI mem_Collect_eq snd_conv subsetI that)

  have \<open>(prod b \<longlongrightarrow> a) FA\<close>
  proof (rule tendsto_iff_uniformity[THEN iffD2, rule_format])
    fix E :: \<open>('c \<times> 'c) \<Rightarrow> bool\<close>
    assume \<open>eventually E uniformity\<close>
    then obtain D where D_uni: \<open>eventually D uniformity\<close> and DDE': \<open>\<And>x y z. D (x, y) \<Longrightarrow> D (y, z) \<Longrightarrow> E (x, z)\<close>
      by (metis (no_types, lifting) \<open>eventually E uniformity\<close> uniformity_transE)
    from sum_S obtain G where \<open>finite G\<close> and \<open>G \<subseteq> Sigma A B\<close>
      and G_sum: \<open>G \<subseteq> H \<Longrightarrow> H \<subseteq> Sigma A B \<Longrightarrow> finite H \<Longrightarrow> D (prod f H, a)\<close> for H
      unfolding tendsto_iff_uniformity
      by (metis (mono_tags, lifting) D_uni F_def eventually_finite_subsets_at_top)
    have \<open>finite (fst ` G)\<close> and \<open>fst ` G \<subseteq> A\<close>
      using \<open>finite G\<close> \<open>G \<subseteq> Sigma A B\<close> by auto
    thm uniformity_prod_def
    define Ga where \<open>Ga a = {b. (a,b) \<in> G}\<close> for a
    have Ga_fin: \<open>finite (Ga a)\<close> and Ga_B: \<open>Ga a \<subseteq> B a\<close> for a
      using \<open>finite G\<close> \<open>G \<subseteq> Sigma A B\<close> finite_proj by (auto simp: Ga_def finite_proj)

    have \<open>E (prod b M, a)\<close> if \<open>M \<supseteq> fst ` G\<close> and \<open>finite M\<close> and \<open>M \<subseteq> A\<close> for M
    proof -
      define FMB where \<open>FMB = finite_subsets_at_top (Sigma M B)\<close>
      have \<open>eventually (\<lambda>H. D (\<Prod>a\<in>M. b a, \<Prod>(a,b)\<in>H. f (a,b))) FMB\<close>
      proof -
        obtain D' where D'_uni: \<open>eventually D' uniformity\<close> 
          and \<open>card M' \<le> card M \<and> (\<forall>m\<in>M'. D' (g m, g' m)) \<Longrightarrow> D (prod g M', prod g' M')\<close>
        for M' :: \<open>'a set\<close> and g g'
          using prod_uniformity[OF times_cont \<open>eventually D uniformity\<close>] by blast
        then have D'_sum_D: \<open>(\<forall>m\<in>M. D' (g m, g' m)) \<Longrightarrow> D (prod g M, prod g' M)\<close> for g g'
          by auto

        obtain Ha where \<open>Ha a \<supseteq> Ga a\<close> and Ha_fin: \<open>finite (Ha a)\<close> and Ha_B: \<open>Ha a \<subseteq> B a\<close>
          and D'_sum_Ha: \<open>Ha a \<subseteq> L \<Longrightarrow> L \<subseteq> B a \<Longrightarrow> finite L \<Longrightarrow> D' (b a, prod (\<lambda>b. f (a,b)) L)\<close> if \<open>a \<in> A\<close> for a L
        proof -
          from sum_b[unfolded tendsto_iff_uniformity, rule_format, OF _ D'_uni[THEN uniformity_sym]]
          obtain Ha0 where \<open>finite (Ha0 a)\<close> and \<open>Ha0 a \<subseteq> B a\<close>
            and \<open>Ha0 a \<subseteq> L \<Longrightarrow> L \<subseteq> B a \<Longrightarrow> finite L \<Longrightarrow> D' (b a, prod (\<lambda>b. f (a,b)) L)\<close> if \<open>a \<in> A\<close> for a L
            unfolding FB_def eventually_finite_subsets_at_top unfolding prod.case by metis
          moreover define Ha where \<open>Ha a = Ha0 a \<union> Ga a\<close> for a
          ultimately show ?thesis
            using that[where Ha=Ha]
            using Ga_fin Ga_B by auto
        qed

        have \<open>D (\<Prod>a\<in>M. b a, \<Prod>(a,b)\<in>H. f (a,b))\<close> if \<open>finite H\<close> and \<open>H \<subseteq> Sigma M B\<close> and \<open>H \<supseteq> Sigma M Ha\<close> for H
        proof -
          define Ha' where \<open>Ha' a = {b| b. (a,b) \<in> H}\<close> for a
          have [simp]: \<open>finite (Ha' a)\<close> and [simp]: \<open>Ha' a \<supseteq> Ha a\<close> and [simp]: \<open>Ha' a \<subseteq> B a\<close> if \<open>a \<in> M\<close> for a
            unfolding Ha'_def using \<open>finite H\<close> \<open>H \<subseteq> Sigma M B\<close> \<open>Sigma M Ha \<subseteq> H\<close> that finite_proj by auto
          have \<open>Sigma M Ha' = H\<close>
            using that by (auto simp: Ha'_def)
          then have *: \<open>(\<Prod>(a,b)\<in>H. f (a,b)) = (\<Prod>a\<in>M. \<Prod>b\<in>Ha' a. f (a,b))\<close>
            by (simp add: \<open>finite M\<close> prod.Sigma)
          have \<open>D' (b a, prod (\<lambda>b. f (a,b)) (Ha' a))\<close> if \<open>a \<in> M\<close> for a
            using D'_sum_Ha \<open>M \<subseteq> A\<close> that by auto
          then have \<open>D (\<Prod>a\<in>M. b a, \<Prod>a\<in>M. prod (\<lambda>b. f (a,b)) (Ha' a))\<close>
            by (rule_tac D'_sum_D, auto)
          with * show ?thesis
            by auto
        qed
        moreover have \<open>Sigma M Ha \<subseteq> Sigma M B\<close>
          using Ha_B \<open>M \<subseteq> A\<close> by auto
        ultimately show ?thesis
          unfolding FMB_def eventually_finite_subsets_at_top
          by (metis (no_types, lifting) Ha_fin finite_SigmaI subsetD that(2) that(3))
      qed
      moreover have \<open>eventually (\<lambda>H. D (\<Prod>(a,b)\<in>H. f (a,b), a)) FMB\<close>
        unfolding FMB_def eventually_finite_subsets_at_top
      proof (rule exI[of _ G], safe)
        fix Y assume Y: "finite Y" "G \<subseteq> Y" "Y \<subseteq> Sigma M B"
        thus "D (\<Prod>(a,b)\<in>Y. f (a, b), a)"
          using G_sum[of Y] Y using that(3) by fastforce
      qed (use \<open>finite G\<close> \<open>G \<subseteq> Sigma A B\<close> that in auto)
      ultimately have \<open>\<forall>\<^sub>F x in FMB. E (prod b M, a)\<close>
        by eventually_elim (use DDE' in auto)
      then show \<open>E (prod b M, a)\<close>
        using FMB_def by force
    qed
    then show \<open>\<forall>\<^sub>F x in FA. E (prod b x, a)\<close>
      using \<open>finite (fst ` G)\<close> and \<open>fst ` G \<subseteq> A\<close>
      by (metis (mono_tags, lifting) FA_def eventually_finite_subsets_at_top)
  qed
  then show ?thesis
    by (simp add: FA_def has_setprod_def)
qed

lemma multipliable_on_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{field, topological_semigroup_mult, t2_space, uniform_space}\<close>
  assumes times_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x*y)\<close>
  assumes multipliableAB: "(\<lambda>(x,y). f x y) multipliable_on (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x) multipliable_on (B x)\<close>
  shows \<open>(\<lambda>x. infprod (f x) (B x)) multipliable_on A\<close>
proof -
  from multipliableAB obtain a where a: \<open>((\<lambda>(x,y). f x y) has_setprod a) (Sigma A B)\<close>
    using has_setprod_infprod by blast
  from multipliableB have b: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x has_setprod infprod (f x) (B x)) (B x)\<close>
    by (auto intro!: has_setprod_infprod)
  show ?thesis
    using times_cont a b
    by (smt (verit) has_setprod_Sigma[where f=\<open>\<lambda>(x,y). f x y\<close>] has_setprod_cong old.prod.case multipliable_on_def) 
qed

lemma infprod_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{field, topological_semigroup_mult, t2_space, uniform_space}\<close>
  assumes times_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x*y)\<close>
  assumes multipliableAB: "f multipliable_on (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (\<lambda>y. f (x, y)) multipliable_on (B x)\<close>
  shows "infprod f (Sigma A B) = infprod (\<lambda>x. infprod (\<lambda>y. f (x, y)) (B x)) A"
proof -
  from multipliableAB have a: \<open>(f has_setprod infprod f (Sigma A B)) (Sigma A B)\<close>
    using has_setprod_infprod by blast
  from multipliableB have b: \<open>\<And>x. x\<in>A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod infprod (\<lambda>y. f (x, y)) (B x)) (B x)\<close>
    by (auto intro!: has_setprod_infprod)
  show ?thesis
    using times_cont a b by (auto intro: infprodI[symmetric] has_setprod_Sigma simp: multipliable_on_def)
qed

lemma infprod_Sigma':
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{field, topological_semigroup_mult, t2_space, uniform_space}\<close>
  assumes times_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x*y)\<close>
  assumes multipliableAB: "(\<lambda>(x,y). f x y) multipliable_on (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x) multipliable_on (B x)\<close>
  shows \<open>infprod (\<lambda>x. infprod (f x) (B x)) A = infprod (\<lambda>(x,y). f x y) (Sigma A B)\<close>
  using infprod_Sigma[of \<open>\<lambda>(x,y). f x y\<close> A B]
  using assms by auto

lemma isUCont_times[simp]:
  shows \<open>isUCont (\<lambda>(x::'a::real_normed_algebra,y). x*y)\<close>
  sorry

lemma
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{banach,real_normed_field}\<close>
  assumes [simp]: "(\<lambda>(x,y). f x y) multipliable_on (Sigma A B)"
  shows infprod_Sigma'_banach: \<open>infprod (\<lambda>x. infprod (f x) (B x)) A = infprod (\<lambda>(x,y). f x y) (Sigma A B)\<close> (is ?thesis1)
    and multipliable_on_Sigma_banach: \<open>(\<lambda>x. infprod (f x) (B x)) multipliable_on A\<close> (is ?thesis2)
proof -
  have fprod: \<open>(f x) multipliable_on (B x)\<close> if \<open>x \<in> A\<close> for x
  proof -
    from assms
    have \<open>(\<lambda>(x,y). f x y) multipliable_on (Pair x ` B x)\<close>
      by (meson image_subset_iff multipliable_on_subset_banach mem_Sigma_iff that)
    then have \<open>((\<lambda>(x,y). f x y) \<circ> Pair x) multipliable_on (B x)\<close>
      by (metis multipliable_on_reindex inj_on_def prod.inject)
    then show ?thesis
      by (auto simp: o_def)
  qed
  show ?thesis1
    using fprod assms infprod_Sigma' isUCont_times by blast
  show ?thesis2
    using fprod assms isUCont_times multipliable_on_Sigma by blast
qed

lemma infprod_Sigma_banach:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{banach,real_normed_field}\<close>
  assumes [simp]: "f multipliable_on (Sigma A B)"
  shows \<open>infprod (\<lambda>x. infprod (\<lambda>y. f (x,y)) (B x)) A = infprod f (Sigma A B)\<close>
  using assms by (simp add: infprod_Sigma'_banach)

lemma infprod_swap:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::{field, topological_semigroup_mult, t2_space, uniform_space}"
  assumes times_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x*y)\<close>
  assumes \<open>(\<lambda>(x, y). f x y) multipliable_on (A \<times> B)\<close>
  assumes \<open>\<And>a. a\<in>A \<Longrightarrow> (f a) multipliable_on B\<close>
  assumes \<open>\<And>b. b\<in>B \<Longrightarrow> (\<lambda>a. f a b) multipliable_on A\<close>
  shows \<open>infprod (\<lambda>x. infprod (\<lambda>y. f x y) B) A = infprod (\<lambda>y. infprod (\<lambda>x. f x y) A) B\<close>
proof -
  have "(\<lambda>(x, y). f y x) \<circ> prod.swap multipliable_on A \<times> B"
    by (simp add: assms(2) multipliable_on_cong)
  then have fyx: \<open>(\<lambda>(x, y). f y x) multipliable_on (B \<times> A)\<close>
    by (metis has_setprod_reindex infprod_reindex inj_swap product_swap multipliable_iff_has_setprod_infprod)
  have \<open>infprod (\<lambda>x. infprod (\<lambda>y. f x y) B) A = infprod (\<lambda>(x,y). f x y) (A \<times> B)\<close>
    using assms infprod_Sigma' by blast
  also have \<open>\<dots> = infprod (\<lambda>(x,y). f y x) (B \<times> A)\<close>
    apply (subst product_swap[symmetric])
    apply (subst infprod_reindex)
    using assms by (auto simp: o_def)
  also have \<open>\<dots> = infprod (\<lambda>y. infprod (\<lambda>x. f x y) A) B\<close>
    by (subst infprod_Sigma') (use assms(1,4) fyx in auto)
  finally show ?thesis .
qed

lemma infprod_swap_banach:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::{banach,real_normed_field}"
  assumes \<open>(\<lambda>(x, y). f x y) multipliable_on (A \<times> B)\<close>
  shows "infprod (\<lambda>x. infprod (\<lambda>y. f x y) B) A = infprod (\<lambda>y. infprod (\<lambda>x. f x y) A) B"
proof -
  have \<section>: \<open>(\<lambda>(x, y). f y x) multipliable_on (B \<times> A)\<close>
    by (metis (mono_tags, lifting) assms case_swap inj_swap o_apply product_swap multipliable_on_cong multipliable_on_reindex)
  have \<open>infprod (\<lambda>x. infprod (\<lambda>y. f x y) B) A = infprod (\<lambda>(x,y). f x y) (A \<times> B)\<close>
    using assms infprod_Sigma'_banach by blast
  also have \<open>\<dots> = infprod (\<lambda>(x,y). f y x) (B \<times> A)\<close>
    apply (subst product_swap[symmetric])
    apply (subst infprod_reindex)
    using assms by (auto simp: o_def)
  also have \<open>\<dots> = infprod (\<lambda>y. infprod (\<lambda>x. f x y) A) B\<close>
    by (metis (mono_tags, lifting) \<section> infprod_Sigma'_banach infprod_cong)
  finally show ?thesis .
qed

lemma has_setprod_constant[simp]:
  assumes \<open>finite F\<close>
  shows \<open>((\<lambda>_. c) has_setprod c ^ card F) F\<close>
  by (metis assms has_setprod_finite prod_constant)

lemma infprod_constant[simp]:
  assumes \<open>finite F\<close>
  shows \<open>infprod (\<lambda>_. c) F = c ^ card F\<close>
  by (simp add: assms)

lemma has_setprod_power:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "(f has_setprod P) A"
  shows   "((\<lambda>x. f x ^ n) has_setprod (P ^ n)) A"
  using assms by (induction n) (auto intro!: has_setprod_mult)

lemma multipliable_on_power:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A"
  shows   "(\<lambda>x. f x ^ n) multipliable_on A"
  using assms by (induction n) (auto intro!: multipliable_on_mult)

lemma infprod_power:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A"
  shows \<open>infprod (\<lambda>x. f x ^ n) A = infprod f A ^ n\<close>
  using assms by (simp add: has_setprod_power infprodI)

lemma has_setprod_inverse:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "(f has_setprod (inverse a)) A"
  shows   \<open>((\<lambda>x. inverse (f x)) has_setprod a) A\<close>
  sorry

lemma has_setprod_inverse_iff:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  shows \<open>((\<lambda>x. inverse (f x)) has_setprod a) A \<longleftrightarrow> (f has_setprod (inverse a)) A\<close>
  sorry

lemma multipliable_on_inverse:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A"
  shows   "(\<lambda>x. inverse (f x)) multipliable_on A"
  using has_setprod_inverse assms by (metis inverse_inverse_eq multipliable_on_def)

lemma multipliable_on_inverse_iff:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  shows "(\<lambda>x. inverse (f x)) multipliable_on A \<longleftrightarrow> f multipliable_on A"
  using multipliable_on_inverse inverse_inverse_eq by force

lemma infprod_inverse:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  shows \<open>infprod (\<lambda>x. inverse (f x)) A = inverse (infprod f A)\<close>
  by (metis (full_types) has_setprod_infprod has_setprod_inverse_iff infprodI infprod_not_exists 
                         inverse_1 inverse_inverse_eq)

lemma has_setprod_power_int:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "(f has_setprod P) A"
  shows   "((\<lambda>x. f x powi n) has_setprod (P powi n)) A"
  by (cases "n \<ge> 0") (auto simp: power_int_def intro!: has_setprod_power has_setprod_inverse assms)

lemma multipliable_on_power_int:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A"
  shows   "(\<lambda>x. f x powi n) multipliable_on A"
  by (cases "n \<ge> 0") (auto simp: power_int_def intro!: multipliable_on_power multipliable_on_inverse assms)

lemma infprod_power_int:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "(f has_setprod P) A"
  shows \<open>infprod (\<lambda>x. f x powi n) A = infprod f A powi n\<close>
  sorry

lemma has_sum_imp_has_prod_exp:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "(f has_sum S) A"
  shows   "((\<lambda>x. exp (f x)) has_setprod exp S) A"
proof (rule has_setprodI)
  have "((\<lambda>X. exp (sum f X)) \<longlongrightarrow> exp S) (finite_subsets_at_top A)"
    using assms by (intro tendsto_exp) (auto simp: has_sum_def)
  also have "?this \<longleftrightarrow> ((\<lambda>X. (\<Prod>x\<in>X. exp (f x))) \<longlongrightarrow> exp S) (finite_subsets_at_top A)"
    by (intro filterlim_cong refl eventually_finite_subsets_at_top_weakI) (auto simp: exp_sum)
  finally show "((\<lambda>X. (\<Prod>x\<in>X. exp (f x))) \<longlongrightarrow> exp S) (finite_subsets_at_top A)" .
qed

lemma has_setprod_imp_multipliable: "(f has_setprod S) A \<Longrightarrow> f multipliable_on A"
  by (auto simp: multipliable_on_def)

lemma has_setprod_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "((\<lambda>x. f (g x)) has_setprod S) A = (f has_setprod S) B"
proof -
  have "((\<lambda>x. f (g x)) has_setprod S) A \<longleftrightarrow> (f has_setprod S) (g ` A)"
    by (subst has_setprod_reindex) (use assms in \<open>auto dest: bij_betw_imp_inj_on simp: o_def\<close>)
  then show ?thesis
    using assms bij_betw_imp_surj_on by blast 
qed

lemma has_setprod_reindex_bij_witness:
  assumes "\<And>a. a \<in> S \<Longrightarrow> i (j a) = a"
  assumes "\<And>a. a \<in> S \<Longrightarrow> j a \<in> T"
  assumes "\<And>b. b \<in> T \<Longrightarrow> j (i b) = b"
  assumes "\<And>b. b \<in> T \<Longrightarrow> i b \<in> S"
  assumes "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  assumes "s = s'"
  shows   "(g has_setprod s) S = (h has_setprod s') T"
  by (smt (verit, del_insts) assms bij_betwI' has_setprod_cong has_setprod_reindex_bij_betw)


lemma has_setprod_homomorphism:
  assumes "(f has_setprod S) A" "h 1 = 1" "\<And>a b. h (a * b) = h a * h b" "continuous_on UNIV h"
  shows   "((\<lambda>x. h (f x)) has_setprod (h S)) A"
proof -
  have "prod (h \<circ> f) X = h (prod f X)" for X
    by (induction X rule: infinite_finite_induct) (simp_all add: assms)
  hence prod_h: "prod (h \<circ> f) = h \<circ> prod f"
    by (intro ext) auto
  have "((\<lambda>x. h (prod f x)) \<longlongrightarrow> h S) (finite_subsets_at_top A)"
    by (rule continuous_on_tendsto_compose[OF assms(4) has_setprodD[OF assms(1)]]) auto
  hence "((h \<circ> f) has_setprod h S) A"
    unfolding has_setprod_def prod_h unfolding o_def by simp
  thus ?thesis
    by (simp add: o_def)
qed

lemma multipliable_on_homomorphism:
  assumes "f multipliable_on A" "h 1 = 1" "\<And>a b. h (a * b) = h a * h b" "continuous_on UNIV h"
  shows   "(\<lambda>x. h (f x)) multipliable_on A"
proof -
  from assms(1) obtain S where "(f has_setprod S) A"
    by (auto simp: multipliable_on_def)
  hence "((\<lambda>x. h (f x)) has_setprod h S) A"
    by (rule has_setprod_homomorphism) (use assms in auto)
  thus ?thesis
    by (auto simp: multipliable_on_def)
qed

lemma infprod_homomorphism_strong:
  fixes h :: "'a :: {t2_space, topological_comm_monoid_mult, semidom} \<Rightarrow>
                'b :: {t2_space, topological_comm_monoid_mult, semidom}"
  assumes "(\<lambda>x. h (f x)) multipliable_on A \<longleftrightarrow> f multipliable_on A"
  assumes "h 1 = 1"
  assumes "\<And>S. (f has_setprod S) A \<Longrightarrow> ((\<lambda>x. h (f x)) has_setprod (h S)) A"
  shows   "infprod (\<lambda>x. h (f x)) A = h (infprod f A)"
  by (metis assms has_setprod_infprod infprodI infprod_not_exists)

lemma has_setprod_of_nat: "(f has_setprod S) A \<Longrightarrow> ((\<lambda>x. of_nat (f x)) has_setprod of_nat S) A"
  by (erule has_setprod_homomorphism) (auto intro!: continuous_intros)

lemma has_setprod_of_int: "(f has_setprod S) A \<Longrightarrow> ((\<lambda>x. of_int (f x)) has_setprod of_int S) A"
  by (erule has_setprod_homomorphism) (auto intro!: continuous_intros)

lemma multipliable_on_of_nat: "f multipliable_on A \<Longrightarrow> (\<lambda>x. of_nat (f x)) multipliable_on A"
  by (erule multipliable_on_homomorphism) (auto intro!: continuous_intros)

lemma multipliable_on_of_int: "f multipliable_on A \<Longrightarrow> (\<lambda>x. of_int (f x)) multipliable_on A"
  by (erule multipliable_on_homomorphism) (auto intro!: continuous_intros)

lemma multipliable_on_discrete_iff:
  fixes f :: "'a \<Rightarrow> 'b :: {discrete_topology, topological_comm_monoid_mult, semidom}"
  shows "f multipliable_on A \<longleftrightarrow> (\<exists>x\<in>A. f x = 0) \<or> finite {x\<in>A. f x \<noteq> 1}"
  oops
(*
proof
  assume *: "finite {x\<in>A. f x \<noteq> 1}"
  hence "f multipliable_on {x\<in>A. f x \<noteq> 1}"
    by (rule multipliable_on_finite)
  then show "f multipliable_on A"
    by (smt (verit) DiffE mem_Collect_eq multipliable_on_cong_neutral) 
next
  assume "f multipliable_on A"
  then obtain S where "(f has_setprod S) A"
    by (auto simp: multipliable_on_def)
  hence "\<forall>\<^sub>F x in finite_subsets_at_top A. prod f x = S"
    unfolding has_setprod_def tendsto_discrete .
  then obtain X where X: "finite X" "X \<subseteq> A" "\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod f Y = S"
    unfolding eventually_finite_subsets_at_top by metis
  have "{x\<in>A. f x \<noteq> 1} \<subseteq> X"
  proof
    fix x assume x: "x \<in> {x\<in>A. f x \<noteq> 1}"
    show "x \<in> X"
    proof (rule ccontr)
      assume [simp]: "x \<notin> X"
      have "prod f (insert x X) = S"
        using X x by (intro X) auto
      then have "f x = 1"
        using X by auto
      with x show False
        by auto
    qed
  qed
  thus "finite {x\<in>A. f x \<noteq> 0}"
    using X(1) finite_subset by blast
qed
*)

lemma has_setprod_imp_has_prod: "(f has_setprod S) (UNIV :: nat set) \<Longrightarrow> f has_prod S"
  sorry

lemma multipliable_on_imp_convergent_prod: "f multipliable_on (UNIV :: nat set) \<Longrightarrow> convergent_prod f"
  sorry



subsection \<open>Absolute convergence\<close>

(* Logically belongs in the section about reals, but needed as a dependency here *)
lemma multipliable_on_iff_abs_multipliable_on_real:
  fixes f :: \<open>'a \<Rightarrow> real\<close>
  shows \<open>f multipliable_on A \<longleftrightarrow> f abs_multipliable_on A\<close>
proof (rule iffI)
  assume \<open>f multipliable_on A\<close>
  define n A\<^sub>p A\<^sub>n
    where \<open>n \<equiv> \<lambda>x. norm (f x)\<close> and \<open>A\<^sub>p = {x\<in>A. f x \<ge> 0}\<close> and \<open>A\<^sub>n = {x\<in>A. f x < 0}\<close> for x
  have A: \<open>A\<^sub>p \<union> A\<^sub>n = A\<close> \<open>A\<^sub>p \<inter> A\<^sub>n = {}\<close>
    by (auto simp: A\<^sub>p_def A\<^sub>n_def)
  from \<open>f multipliable_on A\<close> have \<open>f multipliable_on A\<^sub>p\<close> \<open>f multipliable_on A\<^sub>n\<close>
    using A\<^sub>p_def A\<^sub>n_def multipliable_on_subset_banach by fastforce+
  then have \<open>n multipliable_on A\<^sub>p\<close>
    by (smt (verit) A\<^sub>p_def n_def mem_Collect_eq real_norm_def multipliable_on_cong)
  moreover have \<open>n multipliable_on A\<^sub>n\<close>
    by (smt (verit, best) \<open>f multipliable_on A\<^sub>n\<close>  multipliable_on_uminus A\<^sub>n_def n_def multipliable_on_cong mem_Collect_eq real_norm_def)
  ultimately show \<open>n multipliable_on A\<close>
    using A multipliable_on_Un_disjoint by blast
next
  show \<open>f abs_multipliable_on A \<Longrightarrow> f multipliable_on A\<close>
    using abs_multipliable_multipliable by blast
qed

lemma abs_multipliable_on_Sigma_iff:
  shows   "f abs_multipliable_on Sigma A B \<longleftrightarrow>
             (\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_multipliable_on B x) \<and>
             ((\<lambda>x. infprod (\<lambda>y. norm (f (x, y))) (B x)) abs_multipliable_on A)"
proof (intro iffI conjI ballI)
  assume asm: \<open>f abs_multipliable_on Sigma A B\<close>
  then have \<open>(\<lambda>x. infprod (\<lambda>y. norm (f (x,y))) (B x)) multipliable_on A\<close>
    by (simp add: cond_case_prod_eta multipliable_on_Sigma_banach)
  then show \<open>(\<lambda>x. \<Prod>\<^sub>\<infinity>y\<in>B x. norm (f (x, y))) abs_multipliable_on A\<close>
    using multipliable_on_iff_abs_multipliable_on_real by force

  show \<open>(\<lambda>y. f (x, y)) abs_multipliable_on B x\<close> if \<open>x \<in> A\<close> for x
  proof -
    from asm have \<open>f abs_multipliable_on Pair x ` B x\<close>
      by (simp add: image_subset_iff multipliable_on_subset_banach that)
    then show ?thesis
      by (metis (mono_tags, lifting) o_def inj_on_def multipliable_on_reindex prod.inject multipliable_on_cong)
  qed
next
  assume asm: \<open>(\<forall>x\<in>A. (\<lambda>xa. f (x, xa)) abs_multipliable_on B x) \<and>
    (\<lambda>x. \<Prod>\<^sub>\<infinity>y\<in>B x. norm (f (x, y))) abs_multipliable_on A\<close>
  have \<open>(\<Prod>xy\<in>F. norm (f xy)) \<le> (\<Prod>\<^sub>\<infinity>x\<in>A. \<Prod>\<^sub>\<infinity>y\<in>B x. norm (f (x, y)))\<close>
    if \<open>F \<subseteq> Sigma A B\<close> and [simp]: \<open>finite F\<close> for F
  proof -
    have [simp]: \<open>(SIGMA x:fst ` F. {y. (x, y) \<in> F}) = F\<close>
      by (auto intro!: set_eqI simp add: Domain.DomainI fst_eq_Domain)
    have [simp]: \<open>finite {y. (x, y) \<in> F}\<close> for x
      by (metis \<open>finite F\<close> Range.intros finite_Range finite_subset mem_Collect_eq subsetI)
    have \<open>(\<Prod>xy\<in>F. norm (f xy)) = (\<Prod>x\<in>fst ` F. \<Prod>y\<in>{y. (x,y)\<in>F}. norm (f (x,y)))\<close>
      by (simp add: prod.Sigma)
    also have \<open>\<dots> = (\<Prod>\<^sub>\<infinity>x\<in>fst ` F. \<Prod>\<^sub>\<infinity>y\<in>{y. (x,y)\<in>F}. norm (f (x,y)))\<close>
      by auto
    also have \<open>\<dots> \<le> (\<Prod>\<^sub>\<infinity>x\<in>fst ` F. \<Prod>\<^sub>\<infinity>y\<in>B x. norm (f (x,y)))\<close>
      using asm that(1) by (intro infprod_mono infprod_mono_neutral) auto
    also have \<open>\<dots> \<le> (\<Prod>\<^sub>\<infinity>x\<in>A. \<Prod>\<^sub>\<infinity>y\<in>B x. norm (f (x,y)))\<close>
      by (rule infprod_mono_neutral) (use asm that(1) in \<open>auto simp add: infprod_nonneg\<close>)
    finally show ?thesis .
  qed
  then show \<open>f abs_multipliable_on Sigma A B\<close>
    by (intro nonneg_bdd_above_multipliable_on) (auto simp: bdd_above_def)
qed

lemma abs_multipliable_on_comparison_test:
  assumes "g abs_multipliable_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (f x) \<le> norm (g x)"
  shows   "f abs_multipliable_on A"
proof (rule nonneg_bdd_above_multipliable_on)
  show "bdd_above (prod (\<lambda>x. norm (f x)) ` {F. F \<subseteq> A \<and> finite F})"
  proof (rule bdd_aboveI2)
    fix F assume F: "F \<in> {F. F \<subseteq> A \<and> finite F}"
    have \<open>prod (\<lambda>x. norm (f x)) F \<le> prod (\<lambda>x. norm (g x)) F\<close>
      using assms F by (intro sum_mono) auto
    also have \<open>\<dots> = infprod (\<lambda>x. norm (g x)) F\<close>
      using F by simp
    also have \<open>\<dots> \<le> infprod (\<lambda>x. norm (g x)) A\<close>
      by (smt (verit) F assms(1) infprod_mono2 mem_Collect_eq norm_ge_zero multipliable_on_subset_banach)
    finally show "(\<Prod>x\<in>F. norm (f x)) \<le> (\<Prod>\<^sub>\<infinity>x\<in>A. norm (g x))" .
  qed
qed auto

lemma abs_multipliable_iff_bdd_above:
  fixes f :: \<open>'a \<Rightarrow> 'b::real_normed_vector\<close>
  shows \<open>f abs_multipliable_on A \<longleftrightarrow> bdd_above (prod (\<lambda>x. norm (f x)) ` {F. F\<subseteq>A \<and> finite F})\<close>
proof (rule iffI)
  assume \<open>f abs_multipliable_on A\<close>
  show \<open>bdd_above (prod (\<lambda>x. norm (f x)) ` {F. F \<subseteq> A \<and> finite F})\<close>
  proof (rule bdd_aboveI2)
    fix F assume F: "F \<in> {F. F \<subseteq> A \<and> finite F}"
    show "(\<Prod>x\<in>F. norm (f x)) \<le> (\<Prod>\<^sub>\<infinity>x\<in>A. norm (f x))"
      by (rule finite_sum_le_infprod) (use \<open>f abs_multipliable_on A\<close> F in auto)
  qed
next
  assume \<open>bdd_above (prod (\<lambda>x. norm (f x)) ` {F. F\<subseteq>A \<and> finite F})\<close>
  then show \<open>f abs_multipliable_on A\<close>
    by (simp add: nonneg_bdd_above_multipliable_on)
qed

lemma abs_multipliable_product:
  fixes x :: "'a \<Rightarrow> 'b::{real_normed_div_algebra,banach,second_countable_topology}"
  assumes x2_sum: "(\<lambda>i. (x i) * (x i)) abs_multipliable_on A"
    and y2_sum: "(\<lambda>i. (y i) * (y i)) abs_multipliable_on A"
  shows "(\<lambda>i. x i * y i) abs_multipliable_on A"
proof (rule nonneg_bdd_above_multipliable_on)
  show "bdd_above (prod (\<lambda>xa. norm (x xa * y xa)) ` {F. F \<subseteq> A \<and> finite F})"
  proof (rule bdd_aboveI2)
    fix F assume F: \<open>F \<in> {F. F \<subseteq> A \<and> finite F}\<close>
    then have r1: "finite F" and b4: "F \<subseteq> A"
      by auto
  
    have a1: "(\<Prod>\<^sub>\<infinity>i\<in>F. norm (x i * x i)) \<le> (\<Prod>\<^sub>\<infinity>i\<in>A. norm (x i * x i))"
      by (metis (no_types, lifting) b4 infprod_mono2 norm_ge_zero multipliable_on_subset_banach x2_sum)

    have "norm (x i * y i) \<le> norm (x i * x i) + norm (y i * y i)" for i
      unfolding norm_mult by (smt mult_left_mono mult_nonneg_nonneg mult_right_mono norm_ge_zero)
    hence "(\<Prod>i\<in>F. norm (x i * y i)) \<le> (\<Prod>i\<in>F. norm (x i * x i) + norm (y i * y i))"
      by (simp add: sum_mono)
    also have "\<dots> = (\<Prod>i\<in>F. norm (x i * x i)) + (\<Prod>i\<in>F. norm (y i * y i))"
      by (simp add: prod.distrib)
    also have "\<dots> = (\<Prod>\<^sub>\<infinity>i\<in>F. norm (x i * x i)) + (\<Prod>\<^sub>\<infinity>i\<in>F. norm (y i * y i))"
      by (simp add: \<open>finite F\<close>)
    also have "\<dots> \<le> (\<Prod>\<^sub>\<infinity>i\<in>A. norm (x i * x i)) + (\<Prod>\<^sub>\<infinity>i\<in>A. norm (y i * y i))"
      using F assms
      by (intro add_mono infprod_mono2) auto
    finally show \<open>(\<Prod>xa\<in>F. norm (x xa * y xa)) \<le> (\<Prod>\<^sub>\<infinity>i\<in>A. norm (x i * x i)) + (\<Prod>\<^sub>\<infinity>i\<in>A. norm (y i * y i))\<close>
      by simp
  qed
qed auto

subsection \<open>Extended reals and nats\<close>

lemma multipliable_on_ennreal[simp]: \<open>(f::_ \<Rightarrow> ennreal) multipliable_on S\<close> and multipliable_on_enat[simp]: \<open>(f::_ \<Rightarrow> enat) multipliable_on S\<close>
  by (simp_all add: nonneg_multipliable_on_complete)

lemma has_setprod_superconst_infinite_ennreal:
  fixes f :: \<open>'a \<Rightarrow> ennreal\<close>
  assumes geqb: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes b: \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "(f has_setprod \<infinity>) S"
proof -
  have \<open>(prod f \<longlongrightarrow> \<infinity>) (finite_subsets_at_top S)\<close>
  proof (rule order_tendstoI)
    fix y :: ennreal assume \<open>y < \<infinity>\<close>
    then have \<open>y / b < \<infinity>\<close> \<open>y < top\<close>
      using b ennreal_divide_eq_top_iff top.not_eq_extremum by force+
    then obtain F where \<open>finite F\<close> and \<open>F \<subseteq> S\<close> and cardF: \<open>card F > y / b\<close>
      using \<open>infinite S\<close>
      by (metis ennreal_Ex_less_of_nat infinite_arbitrarily_large infinity_ennreal_def)
    moreover have \<open>prod f Y > y\<close> if \<open>finite Y\<close> and \<open>F \<subseteq> Y\<close> and \<open>Y \<subseteq> S\<close> for Y
    proof -
      have \<open>y < b * card F\<close>
        by (metis b \<open>y < top\<close> cardF divide_less_ennreal ennreal_mult_eq_top_iff gr_implies_not_zero mult.commute top.not_eq_extremum)
      also have \<open>\<dots> \<le> b * card Y\<close>
        by (meson b card_mono less_imp_le mult_left_mono of_nat_le_iff that)
      also have \<open>\<dots> = prod (\<lambda>_. b) Y\<close>
        by (simp add: mult.commute)
      also have \<open>\<dots> \<le> prod f Y\<close>
        using geqb by (meson subset_eq sum_mono that(3))
      finally show ?thesis .
    qed
    ultimately show \<open>\<forall>\<^sub>F x in finite_subsets_at_top S. y < prod f x\<close>
      unfolding eventually_finite_subsets_at_top by auto
  qed auto
  then show ?thesis
    by (simp add: has_setprod_def)
qed

lemma infprod_superconst_infinite_ennreal:
  fixes f :: \<open>'a \<Rightarrow> ennreal\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "infprod f S = \<infinity>"
  using assms infprodI has_setprod_superconst_infinite_ennreal by blast

lemma infprod_superconst_infinite_ereal:
  fixes f :: \<open>'a \<Rightarrow> ereal\<close>
  assumes geqb: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes b: \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "infprod f S = \<infinity>"
proof -
  obtain b' where b': \<open>e2ennreal b' = b\<close> and \<open>b' > 0\<close>
    using b by blast
  have "0 < e2ennreal b"
    using b' b
    by (metis dual_order.refl enn2ereal_e2ennreal gr_zeroI order_less_le zero_ennreal.abs_eq)
  hence *: \<open>infprod (e2ennreal \<circ> f) S = \<infinity>\<close>
    using assms b'
    by (intro infprod_superconst_infinite_ennreal[where b=b']) (auto intro!: e2ennreal_mono)
  have \<open>infprod f S = infprod (enn2ereal \<circ> (e2ennreal \<circ> f)) S\<close>
    using geqb b by (intro infprod_cong) (fastforce simp: enn2ereal_e2ennreal)
  also have \<open>\<dots> = enn2ereal \<infinity>\<close>
    using * by (simp add: infprod_comm_additive_general continuous_at_enn2ereal nonneg_multipliable_on_complete)
  also have \<open>\<dots> = \<infinity>\<close>
    by simp
  finally show ?thesis .
qed

lemma has_setprod_superconst_infinite_ereal:
  fixes f :: \<open>'a \<Rightarrow> ereal\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "(f has_setprod \<infinity>) S"
  by (metis Infty_neq_0(1) assms infprod_def has_setprod_infprod infprod_superconst_infinite_ereal)

lemma infprod_superconst_infinite_enat:
  fixes f :: \<open>'a \<Rightarrow> enat\<close>
  assumes geqb: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes b: \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "infprod f S = \<infinity>"
proof -
  have \<open>ennreal_of_enat (infprod f S) = infprod (ennreal_of_enat \<circ> f) S\<close>
    by (simp flip: infprod_comm_additive_general)
  also have \<open>\<dots> = \<infinity>\<close>
    by (metis assms(3) b comp_def ennreal_of_enat_0 ennreal_of_enat_le_iff geqb infprod_superconst_infinite_ennreal leD leI)
  also have \<open>\<dots> = ennreal_of_enat \<infinity>\<close>
    by simp
  finally show ?thesis
    by (rule ennreal_of_enat_inj[THEN iffD1])
qed

lemma has_setprod_superconst_infinite_enat:
  fixes f :: \<open>'a \<Rightarrow> enat\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "(f has_setprod \<infinity>) S"
  by (metis assms i0_lb has_setprod_infprod infprod_superconst_infinite_enat nonneg_multipliable_on_complete)

text \<open>This lemma helps to relate a real-valued infprod to a supremum over extended nonnegative reals.\<close>

lemma infprod_nonneg_is_SUPREMUM_ennreal:
  fixes f :: "'a \<Rightarrow> real"
  assumes multipliable: "f multipliable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ennreal (infprod f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (prod f F)))"
proof -
  have \<section>: "\<And>F. \<lbrakk>finite F; F \<subseteq> A\<rbrakk> \<Longrightarrow> prod (ennreal \<circ> f) F = ennreal (prod f F)"
    by (metis (mono_tags, lifting) comp_def fnn subsetD prod.cong sum_ennreal)
  then have \<open>ennreal (infprod f A) = infprod (ennreal \<circ> f) A\<close>
    by (simp add: infprod_comm_additive_general local.multipliable)
  also have \<open>\<dots> = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (prod f F)))\<close>
    by (metis (mono_tags, lifting) \<section> image_cong mem_Collect_eq nonneg_infprod_complete zero_le)
  finally show ?thesis .
qed

text \<open>This lemma helps to related a real-valued infprod to a supremum over extended reals.\<close>

lemma infprod_nonneg_is_SUPREMUM_ereal:
  fixes f :: "'a \<Rightarrow> real"
  assumes multipliable: "f multipliable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ereal (infprod f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (prod f F)))"
proof -
  have "\<And>F. \<lbrakk>finite F; F \<subseteq> A\<rbrakk> \<Longrightarrow> prod (ereal \<circ> f) F = ereal (prod f F)"
    by auto
  then have \<open>ereal (infprod f A) = infprod (ereal \<circ> f) A\<close>
    by (simp add: infprod_comm_additive_general local.multipliable)
  also have \<open>\<dots> = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (prod f F)))\<close>
    by (subst nonneg_infprod_complete) (simp_all add: assms)
  finally show ?thesis .
qed


subsection \<open>Real numbers\<close>

text \<open>Most lemmas in the general property section already apply to real numbers.
      A few ones that are specific to reals are given here.\<close>

lemma infprod_nonneg_is_SUPREMUM_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes multipliable: "f multipliable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "infprod f A = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (prod f F))"
proof -
  have *: "ereal (infprod f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (prod f F)))"
    using assms by (rule infprod_nonneg_is_SUPREMUM_ereal)
  also have "\<dots> = ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (prod f F))"
    by (metis (no_types, lifting) * MInfty_neq_ereal(2) PInfty_neq_ereal(2) SUP_cong abs_eq_infinity_cases ereal_SUP)
  finally show ?thesis by simp
qed


lemma has_setprod_nonneg_SUPREMUM_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f multipliable_on A" and "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "(f has_setprod (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (prod f F))) A"
  by (metis (mono_tags, lifting) assms has_setprod_infprod infprod_nonneg_is_SUPREMUM_real)

lemma multipliable_countable_real:
  fixes f :: \<open>'a \<Rightarrow> real\<close>
  assumes \<open>f multipliable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 0}\<close>
  using abs_multipliable_countable assms multipliable_on_iff_abs_multipliable_on_real by blast

subsection \<open>Complex numbers\<close>

lemma has_setprod_cnj_iff[simp]: 
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>((\<lambda>x. cnj (f x)) has_setprod cnj a) M \<longleftrightarrow> (f has_setprod a) M\<close>
  by (simp add: has_setprod_def lim_cnj del: cnj_prod add: cnj_sum[symmetric, abs_def, of f])

lemma multipliable_on_cnj_iff[simp]:
  "(\<lambda>i. cnj (f i)) multipliable_on A \<longleftrightarrow> f multipliable_on A"
  by (metis complex_cnj_cnj multipliable_on_def has_setprod_cnj_iff)

lemma infprod_cnj[simp]: \<open>infprod (\<lambda>x. cnj (f x)) M = cnj (infprod f M)\<close>
  by (metis complex_cnj_zero infprodI has_setprod_cnj_iff infprod_def multipliable_on_cnj_iff has_setprod_infprod)

lemma has_setprod_Re:
  assumes "(f has_setprod a) M"
  shows "((\<lambda>x. Re (f x)) has_setprod Re a) M"
  using has_setprod_comm_additive[where f=Re]
  using  assms tendsto_Re by (fastforce simp add: o_def additive_def)

lemma infprod_Re:
  assumes "f multipliable_on M"
  shows "infprod (\<lambda>x. Re (f x)) M = Re (infprod f M)"
  by (simp add: assms has_setprod_Re infprodI)

lemma multipliable_on_Re: 
  assumes "f multipliable_on M"
  shows "(\<lambda>x. Re (f x)) multipliable_on M"
  by (metis assms has_setprod_Re multipliable_on_def)

lemma has_setprod_Im:
  assumes "(f has_setprod a) M"
  shows "((\<lambda>x. Im (f x)) has_setprod Im a) M"
  using has_setprod_comm_additive[where f=Im]
  using  assms tendsto_Im by (fastforce simp add: o_def additive_def)

lemma infprod_Im: 
  assumes "f multipliable_on M"
  shows "infprod (\<lambda>x. Im (f x)) M = Im (infprod f M)"
  by (simp add: assms has_setprod_Im infprodI)

lemma multipliable_on_Im: 
  assumes "f multipliable_on M"
  shows "(\<lambda>x. Im (f x)) multipliable_on M"
  by (metis assms has_setprod_Im multipliable_on_def)

lemma nonneg_infprod_le_0D_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "infprod f A \<le> 0"
    and abs_sum: "f multipliable_on A"
    and nneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
    and "x \<in> A"
  shows "f x = 0"
proof -
  have \<open>Im (f x) = 0\<close>
    using assms(4) less_eq_complex_def nneg by auto
  moreover have \<open>Re (f x) = 0\<close>
    using assms by (auto simp add: multipliable_on_Re infprod_Re less_eq_complex_def intro: nonneg_infprod_le_0D[where A=A])
  ultimately show ?thesis
    by (simp add: complex_eqI)
qed

lemma nonneg_has_setprod_le_0D_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "(f has_setprod a) A" and \<open>a \<le> 0\<close>
    and "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0" and "x \<in> A"
  shows "f x = 0"
  by (metis assms infprodI nonneg_infprod_le_0D_complex multipliable_on_def)

text \<open>The lemma @{thm [source] infprod_mono_neutral} above applies to various linear ordered monoids such as the reals but not to the complex numbers.
      Thus we have a separate corollary for those:\<close>

lemma infprod_mono_neutral_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes [simp]: "f multipliable_on A"
    and [simp]: "g multipliable_on B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows \<open>infprod f A \<le> infprod g B\<close>
proof -
  have \<open>infprod (\<lambda>x. Re (f x)) A \<le> infprod (\<lambda>x. Re (g x)) B\<close>
    by (smt (verit) assms infprod_cong infprod_mono_neutral less_eq_complex_def multipliable_on_Re zero_complex.simps(1))
  then have Re: \<open>Re (infprod f A) \<le> Re (infprod g B)\<close>
    by (metis assms(1-2) infprod_Re)
  have \<open>infprod (\<lambda>x. Im (f x)) A = infprod (\<lambda>x. Im (g x)) B\<close>
    by (smt (verit, best) assms(3-5) infprod_cong_neutral less_eq_complex_def zero_complex.simps(2))
  then have Im: \<open>Im (infprod f A) = Im (infprod g B)\<close>
    by (metis assms(1-2) infprod_Im)
  from Re Im show ?thesis
    by (auto simp: less_eq_complex_def)
qed

lemma infprod_mono_complex:
  fixes f g :: "'a \<Rightarrow> complex"
  assumes f_sum: "f multipliable_on A" and g_sum: "g multipliable_on A"
  assumes leq: "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows   "infprod f A \<le> infprod g A"
  by (metis DiffE IntD1 f_prod g_prod infprod_mono_neutral_complex leq)


lemma infprod_nonneg_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "f multipliable_on M"
    and "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infprod f M \<ge> 0" (is "?lhs \<ge> _")
  by (metis assms infprod_0_simp multipliable_on_0_simp infprod_mono_complex)

lemma infprod_cmod:
  assumes "f multipliable_on M"
    and fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infprod (\<lambda>x. cmod (f x)) M = cmod (infprod f M)"
proof -
  have \<open>complex_of_real (infprod (\<lambda>x. cmod (f x)) M) = infprod (\<lambda>x. complex_of_real (cmod (f x))) M\<close>
  proof (rule infprod_comm_additive[symmetric, unfolded o_def])
    have "(\<lambda>z. Re (f z)) multipliable_on M"
      using assms multipliable_on_Re by blast
    also have "?this \<longleftrightarrow> f abs_multipliable_on M"
      using fnn by (intro multipliable_on_cong) (auto simp: less_eq_complex_def cmod_def)
    finally show \<dots> .
  qed (auto simp: additive_def)
  also have \<open>\<dots> = infprod f M\<close>
    using fnn cmod_eq_Re complex_is_Real_iff less_eq_complex_def by (force cong: infprod_cong)
  finally show ?thesis
    by (metis abs_of_nonneg infprod_def le_less_trans norm_ge_zero norm_infprod_bound norm_of_real not_le order_refl)
qed


lemma multipliable_on_iff_abs_multipliable_on_complex:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>f multipliable_on A \<longleftrightarrow> f abs_multipliable_on A\<close>
proof (rule iffI)
  assume \<open>f multipliable_on A\<close>
  define i r ni nr n where \<open>i x = Im (f x)\<close> and \<open>r x = Re (f x)\<close>
    and \<open>ni x = norm (i x)\<close> and \<open>nr x = norm (r x)\<close> and \<open>n x = norm (f x)\<close> for x
  from \<open>f multipliable_on A\<close> have \<open>i multipliable_on A\<close>
    by (simp add: i_def[abs_def] multipliable_on_Im)
  then have [simp]: \<open>ni multipliable_on A\<close>
    using ni_def[abs_def] multipliable_on_iff_abs_multipliable_on_real by force

  from \<open>f multipliable_on A\<close> have \<open>r multipliable_on A\<close>
    by (simp add: r_def[abs_def] multipliable_on_Re)
  then have [simp]: \<open>nr multipliable_on A\<close>
    by (metis nr_def multipliable_on_cong multipliable_on_iff_abs_multipliable_on_real)

  have n_sum: \<open>n x \<le> nr x + ni x\<close> for x
    by (simp add: n_def nr_def ni_def r_def i_def cmod_le)

  have *: \<open>(\<lambda>x. nr x + ni x) multipliable_on A\<close>
    by (simp add: multipliable_on_add)
  have "bdd_above (prod n ` {F. F \<subseteq> A \<and> finite F})"
    apply (rule bdd_aboveI[where M=\<open>infprod (\<lambda>x. nr x + ni x) A\<close>])
    using * n_prod by (auto simp flip: infprod_finite simp: ni_def nr_def intro!: infprod_mono_neutral)
  then show \<open>n multipliable_on A\<close>
    by (simp add: n_def nonneg_bdd_above_multipliable_on)
next
  show \<open>f abs_multipliable_on A \<Longrightarrow> f multipliable_on A\<close>
    using abs_multipliable_multipliable by blast
qed

lemma multipliable_countable_complex:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>f multipliable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 0}\<close>
  using abs_multipliable_countable assms multipliable_on_iff_abs_multipliable_on_complex by blast


(* TODO: figure all this out *)
inductive (in topological_space) convergent_filter :: "'a filter \<Rightarrow> bool" where
  "F \<le> nhds x \<Longrightarrow> convergent_filter F"

lemma (in topological_space) convergent_filter_iff: "convergent_filter F \<longleftrightarrow> (\<exists>x. F \<le> nhds x)"
  by (auto simp: convergent_filter.simps)

lemma (in uniform_space) cauchy_filter_mono:
  "cauchy_filter F \<Longrightarrow> F' \<le> F \<Longrightarrow> cauchy_filter F'"
  unfolding cauchy_filter_def by (meson dual_order.trans prod_filter_mono)

lemma (in uniform_space) convergent_filter_cauchy: 
  assumes "convergent_filter F"
  shows   "cauchy_filter F"
  using assms cauchy_filter_mono nhds_imp_cauchy_filter[OF order.refl]
  by (auto simp: convergent_filter_iff)

lemma (in topological_space) convergent_filter_bot [simp, intro]: "convergent_filter bot"
  by (simp add: convergent_filter_iff)



class complete_uniform_space = uniform_space +
  assumes cauchy_filter_convergent': "cauchy_filter (F :: 'a filter) \<Longrightarrow> F \<noteq> bot \<Longrightarrow> convergent_filter F"

lemma (in complete_uniform_space)
  cauchy_filter_convergent: "cauchy_filter (F :: 'a filter) \<Longrightarrow> convergent_filter F"
  using cauchy_filter_convergent'[of F] by (cases "F = bot") auto

lemma (in complete_uniform_space) convergent_filter_iff_cauchy:
  "convergent_filter F \<longleftrightarrow> cauchy_filter F"
  using convergent_filter_cauchy cauchy_filter_convergent by blast

definition countably_generated_filter :: "'a filter \<Rightarrow> bool" where
  "countably_generated_filter F \<longleftrightarrow> (\<exists>U :: nat \<Rightarrow> 'a set. F = (INF (n::nat). principal (U n)))"

lemma countably_generated_filter_has_antimono_basis:
  assumes "countably_generated_filter F"
  obtains B :: "nat \<Rightarrow> 'a set"
  where "antimono B" and "F = (INF n. principal (B n))" and
        "\<And>P. eventually P F \<longleftrightarrow> (\<exists>i. \<forall>x\<in>B i. P x)"
proof -
  from assms obtain B where B: "F = (INF (n::nat). principal (B n))"
    unfolding countably_generated_filter_def by blast

  define B' where "B' = (\<lambda>n. \<Inter>k\<le>n. B k)"
  have "antimono B'"
    unfolding decseq_def B'_def by force

  have "(INF n. principal (B' n)) = (INF n. INF k\<in>{..n}. principal (B k))"
    unfolding B'_def by (intro INF_cong refl INF_principal_finite [symmetric]) auto
  also have "\<dots> = (INF (n::nat). principal (B n))"
    apply (intro antisym)
    apply (meson INF_lower INF_mono atMost_iff order_refl)
    apply (meson INF_greatest INF_lower UNIV_I)
    done
  also have "\<dots> = F"
    by (simp add: B)
  finally have F: "F = (INF n. principal (B' n))" ..

  moreover have "eventually P F \<longleftrightarrow> (\<exists>i. eventually P (principal (B' i)))" for P
    unfolding F using \<open>antimono B'\<close>
    apply (subst eventually_INF_base)
      apply (auto simp: decseq_def)
    by (meson nat_le_linear)
  ultimately show ?thesis
    using \<open>antimono B'\<close> that[of B'] unfolding eventually_principal by blast
qed

lemma (in uniform_space) cauchy_filter_iff:
  "cauchy_filter F \<longleftrightarrow> (\<forall>P. eventually P uniformity \<longrightarrow> (\<exists>X. eventually (\<lambda>x. x \<in> X) F \<and> (\<forall>z\<in>X\<times>X. P z)))" 
  unfolding cauchy_filter_def le_filter_def
  apply auto
   apply (smt (z3) eventually_mono eventually_prod_same mem_Collect_eq)
  using eventually_prod_same by blast                            

lemma (in uniform_space) controlled_sequences_convergent_imp_complete_aux_sequence:
  fixes U :: "nat \<Rightarrow> ('a \<times> 'a) set"
  fixes F :: "'a filter"
  assumes "cauchy_filter F" "F \<noteq> bot"
  assumes "\<And>n. eventually (\<lambda>z. z \<in> U n) uniformity"
  obtains g G where
    "antimono G" "\<And>n. g n \<in> G n"
    "\<And>n. eventually (\<lambda>x. x \<in> G n) F" "\<And>n. G n \<times> G n \<subseteq> U n"
proof -
  have "\<exists>C. eventually (\<lambda>x. x \<in> C) F \<and> C \<times> C \<subseteq> U n" for n
    using assms(1) assms(3)[of n] unfolding cauchy_filter_iff by blast
  then obtain G where G: "\<And>n. eventually (\<lambda>x. x \<in> G n) F" "\<And>n. G n \<times> G n \<subseteq> U n"
    by metis
  define G' where "G' = (\<lambda>n. \<Inter>k\<le>n. G k)"
  have 1: "eventually (\<lambda>x. x \<in> G' n) F" for n
    using G by (auto simp: G'_def intro: eventually_ball_finite)
  have 2: "G' n \<times> G' n \<subseteq> U n" for n
    using G unfolding G'_def by fast
  have 3: "antimono G'"
    unfolding G'_def decseq_def by force

  have "\<exists>g. g \<in> G' n" for n
    using 1 assms(2) eventually_happens' by auto
  then obtain g where g: "\<And>n. g n \<in> G' n"
    by metis
  from g 1 2 3 that[of G' g] show ?thesis
    by metis
qed

definition lift_filter :: "('a set \<Rightarrow> 'b filter) \<Rightarrow> 'a filter \<Rightarrow> 'b filter" where
  "lift_filter f F = (INF X\<in>{X. eventually (\<lambda>x. x \<in> X) F}. f X)"

lemma lift_filter_top [simp]: "lift_filter g top = g UNIV"
proof -
  have "{X. \<forall>x::'b. x \<in> X} = {UNIV}"
    by auto
  thus ?thesis
    by (simp add: lift_filter_def)
qed

lemma eventually_lift_filter_iff:
  assumes "mono g"
  shows   "eventually P (lift_filter g F) \<longleftrightarrow> (\<exists>X. eventually (\<lambda>x. x \<in> X) F \<and> eventually P (g X))"
  unfolding lift_filter_def
proof (subst eventually_INF_base, goal_cases)
  case 1
  thus ?case by (auto intro: exI[of _ UNIV])
next
  case (2 X Y)
  thus ?case
    by (auto intro!: exI[of _ "X \<inter> Y"] eventually_conj monoD[OF assms])
qed auto

lemma lift_filter_le:
  assumes "eventually (\<lambda>x. x \<in> X) F" "g X \<le> F'"
  shows   "lift_filter g F \<le> F'"
  unfolding lift_filter_def
  by (metis INF_lower2 assms mem_Collect_eq)

definition lift_filter' :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a filter \<Rightarrow> 'b filter" where
  "lift_filter' f F = lift_filter (principal \<circ> f) F"

lemma lift_filter'_top [simp]: "lift_filter' g top = principal (g UNIV)"
  by (simp add: lift_filter'_def)

lemma eventually_lift_filter'_iff:
  assumes "mono g"
  shows   "eventually P (lift_filter' g F) \<longleftrightarrow> (\<exists>X. eventually (\<lambda>x. x \<in> X) F \<and> (\<forall>x\<in>g X. P x))"
  unfolding lift_filter'_def using assms
  by (subst eventually_lift_filter_iff) (auto simp: mono_def eventually_principal)

lemma lift_filter'_le:
  assumes "eventually (\<lambda>x. x \<in> X) F" "principal (g X) \<le> F'"
  shows   "lift_filter' g F \<le> F'"
  unfolding lift_filter'_def using assms
  by (intro lift_filter_le[where X = X]) auto


lemma (in uniform_space) comp_uniformity_le_uniformity:
  "lift_filter' (\<lambda>X. X O X) uniformity \<le> uniformity"
  unfolding le_filter_def
proof safe
  fix P assume P: "eventually P uniformity"
  have [simp]: "mono (\<lambda>X::('a \<times> 'a) set. X O X)"
    by (intro monoI) auto
  from P obtain P' where P': "eventually P' uniformity " "(\<And>x y z. P' (x, y) \<Longrightarrow> P' (y, z) \<Longrightarrow> P (x, z))"
    using uniformity_transE by blast
  show "eventually P (lift_filter' (\<lambda>X. X O X) uniformity)"
    by (auto simp: eventually_lift_filter'_iff intro!: exI[of _ "{x. P' x}"] P')
qed

lemma (in uniform_space) comp_mem_uniformity_sets:
  assumes "eventually (\<lambda>z. z \<in> X) uniformity"
  obtains Y where "eventually (\<lambda>z. z \<in> Y) uniformity" "Y O Y \<subseteq> X"
proof -
  have [simp]: "mono (\<lambda>X::('a \<times> 'a) set. X O X)"
    by (intro monoI) auto
  have "eventually (\<lambda>z. z \<in> X) (lift_filter' (\<lambda>X. X O X) uniformity)"
    using assms comp_uniformity_le_uniformity using filter_leD by blast
  thus ?thesis using that
    by (auto simp: eventually_lift_filter'_iff)
qed

lemma (in uniform_space) le_nhds_of_cauchy_adhp_aux:
  assumes "\<And>P. eventually P uniformity \<Longrightarrow> (\<exists>X. eventually (\<lambda>y. y \<in> X) F \<and> (\<forall>z\<in>X \<times> X. P z) \<and> (\<exists>y. P (x, y) \<and> y \<in> X))"
  shows   "F \<le> nhds x"
  unfolding le_filter_def
proof safe
  fix P assume "eventually P (nhds x)"
  hence "\<forall>\<^sub>F z in uniformity. z \<in> {z. fst z = x \<longrightarrow> P (snd z)}"
    by (simp add: eventually_nhds_uniformity case_prod_unfold)
  then obtain Y where Y: "\<forall>\<^sub>F z in uniformity. z \<in> Y" "Y O Y \<subseteq> {z. fst z = x \<longrightarrow> P (snd z)}"
    using comp_mem_uniformity_sets by blast
  obtain X y where Xy: "eventually (\<lambda>y. y \<in> X) F" "X\<times>X \<subseteq> Y" "(x, y) \<in> Y" "y \<in> X"
    using assms[OF Y(1)] by blast
  have *: "P x" if "x \<in> X" for x
    using Y(2) Xy(2-4) that unfolding relcomp_unfold by force  
  show "eventually P F"
    by (rule eventually_mono[OF Xy(1)]) (use * in auto)
qed

lemma (in uniform_space) eventually_uniformity_imp_nhds:
  assumes "eventually P uniformity"
  shows   "eventually (\<lambda>y. P (x, y)) (nhds x)"
  using assms unfolding eventually_nhds_uniformity by (elim eventually_mono) auto

lemma (in uniform_space) controlled_sequences_convergent_imp_complete_aux:
  fixes U :: "nat \<Rightarrow> ('a \<times> 'a) set"
  assumes gen: "countably_generated_filter (uniformity :: ('a \<times> 'a) filter)"
  assumes U: "\<And>n. eventually (\<lambda>z. z \<in> U n) uniformity"
  assumes conv: "\<And>(u :: nat \<Rightarrow> 'a). (\<And>N m n. N \<le> m \<Longrightarrow> N \<le> n \<Longrightarrow> (u m, u n) \<in> U N) \<Longrightarrow> convergent u"
  assumes "cauchy_filter F"
  shows   "convergent_filter F"
proof (cases "F = bot")
  case False
  note F = \<open>cauchy_filter F\<close> \<open>F \<noteq> bot\<close>
  from gen obtain B :: "nat \<Rightarrow> ('a \<times> 'a) set" where B:
    "antimono B" "uniformity = (INF n. principal (B n))"
    "\<And>P. eventually P uniformity \<longleftrightarrow> (\<exists>i. \<forall>x\<in>B i. P x)"
    using countably_generated_filter_has_antimono_basis by blast

  have ev_B: "eventually (\<lambda>z. z \<in> B n) uniformity" for n
    by (subst B(3)) auto
  hence ev_B': "eventually (\<lambda>z. z \<in> B n \<inter> U n) uniformity" for n
    using U by (auto intro: eventually_conj)

  obtain g G where gG: "antimono G" "\<And>n. g n \<in> G n"
    "\<And>n. eventually (\<lambda>x. x \<in> G n) F" "\<And>n. G n \<times> G n \<subseteq> B n \<inter> U n"
    using controlled_sequences_convergent_imp_complete_aux_sequence[of F "\<lambda>n. B n \<inter> U n", OF F ev_B']
    by metis

  have "convergent g"
  proof (rule conv)
    fix N m n :: nat
    assume mn: "N \<le> m" "N \<le> n"
    have "(g m, g n) \<in> G m \<times> G n"
      using gG by auto
    also from mn have "\<dots> \<subseteq> G N \<times> G N"
      by (intro Sigma_mono gG antimonoD[OF gG(1)])
    also have "\<dots> \<subseteq> U N"
      using gG by blast
    finally show "(g m, g n) \<in> U N" .
  qed
  then obtain L where G: "g \<longlonglongrightarrow> L"
    unfolding convergent_def by blast

  have "F \<le> nhds L"
  proof (rule le_nhds_of_cauchy_adhp_aux)
    fix P :: "'a \<times> 'a \<Rightarrow> bool"
    assume P: "eventually P uniformity"
    hence "eventually (\<lambda>n. \<forall>x\<in>B n. P x) sequentially"
      using \<open>antimono B\<close> unfolding B(3) eventually_sequentially decseq_def by blast
    moreover have "eventually (\<lambda>n. P (L, g n)) sequentially"
      using P eventually_compose_filterlim eventually_uniformity_imp_nhds G by blast
    ultimately have "eventually (\<lambda>n. (\<forall>x\<in>B n. P x) \<and> P (L, g n)) sequentially"
      by eventually_elim auto
    then obtain n where "\<forall>x\<in>B n. P x" "P (L, g n)"
      unfolding eventually_at_top_linorder by blast
    then show "\<exists>X. (\<forall>\<^sub>F y in F. y \<in> X) \<and> (\<forall>z\<in>X \<times> X. P z) \<and> (\<exists>y. P (L, y) \<and> y \<in> X)"
      using gG by blast+
  qed
  thus "convergent_filter F"
    by (auto simp: convergent_filter_iff)
qed auto

theorem (in uniform_space) controlled_sequences_convergent_imp_complete:
  fixes U :: "nat \<Rightarrow> ('a \<times> 'a) set"
  assumes gen: "countably_generated_filter (uniformity :: ('a \<times> 'a) filter)"
  assumes U: "\<And>n. eventually (\<lambda>z. z \<in> U n) uniformity"
  assumes conv: "\<And>(u :: nat \<Rightarrow> 'a). (\<And>N m n. N \<le> m \<Longrightarrow> N \<le> n \<Longrightarrow> (u m, u n) \<in> U N) \<Longrightarrow> convergent u"
  shows "class.complete_uniform_space open uniformity"
  by unfold_locales (use assms controlled_sequences_convergent_imp_complete_aux in blast)

lemma filtermap_prod_filter: "filtermap (map_prod f g) (F \<times>\<^sub>F G) = filtermap f F \<times>\<^sub>F filtermap g G"
proof (intro antisym)
  show "filtermap (map_prod f g) (F \<times>\<^sub>F G) \<le> filtermap f F \<times>\<^sub>F filtermap g G"
    by (auto simp: le_filter_def eventually_filtermap eventually_prod_filter)
next
  show "filtermap f F \<times>\<^sub>F filtermap g G \<le> filtermap (map_prod f g) (F \<times>\<^sub>F G)"
    unfolding le_filter_def
  proof safe
    fix P assume P: "eventually P (filtermap (map_prod f g) (F \<times>\<^sub>F G))"
    then obtain Pf Pg where *: "eventually Pf F" "eventually Pg G" "\<forall>x. Pf x \<longrightarrow> (\<forall>y. Pg y \<longrightarrow> P (f x, g y))"
      by (auto simp: eventually_filtermap eventually_prod_filter)

    define Pf' where "Pf' = (\<lambda>x. \<exists>y. x = f y \<and> Pf y)"
    define Pg' where "Pg' = (\<lambda>x. \<exists>y. x = g y \<and> Pg y)"

    from *(1) have "\<forall>\<^sub>F x in F. Pf' (f x)"
      by eventually_elim (auto simp: Pf'_def)
    moreover from *(2) have "\<forall>\<^sub>F x in G. Pg' (g x)"
      by eventually_elim (auto simp: Pg'_def)
    moreover have "(\<forall>x y. Pf' x \<longrightarrow> Pg' y \<longrightarrow> P (x, y))"
      using *(3) by (auto simp: Pf'_def Pg'_def)
    ultimately show "eventually P (filtermap f F \<times>\<^sub>F filtermap g G)"
      unfolding eventually_prod_filter eventually_filtermap
      by blast
  qed
qed
      

lemma (in uniform_space) Cauchy_seq_iff_tendsto:
  "Cauchy f \<longleftrightarrow> filterlim (map_prod f f) uniformity (at_top \<times>\<^sub>F at_top)"
  unfolding Cauchy_uniform cauchy_filter_def filterlim_def filtermap_prod_filter ..

theorem (in uniform_space) controlled_seq_imp_Cauchy_seq:
  fixes U :: "nat \<Rightarrow> ('a \<times> 'a) set"
  assumes U: "\<And>P. eventually P uniformity \<Longrightarrow> (\<exists>n. \<forall>x\<in>U n. P x)"
  assumes controlled: "\<And>N m n. N \<le> m \<Longrightarrow> N \<le> n \<Longrightarrow> (f m, f n) \<in> U N"
  shows   "Cauchy f"
  unfolding Cauchy_seq_iff_tendsto
proof -
  show "filterlim (map_prod f f) uniformity (sequentially \<times>\<^sub>F sequentially)"
    unfolding filterlim_def le_filter_def
  proof safe
    fix P :: "'a \<times> 'a \<Rightarrow> bool"
    assume P: "eventually P uniformity"
    from U[OF this] obtain N where "\<forall>x\<in>U N. P x"
      by blast
    then show "eventually P (filtermap (map_prod f f) (sequentially \<times>\<^sub>F sequentially))"
      unfolding eventually_filtermap eventually_prod_sequentially
      by (metis controlled map_prod_simp)
  qed
qed

lemma (in uniform_space) Cauchy_seq_convergent_imp_complete_aux:
  fixes U :: "nat \<Rightarrow> ('a \<times> 'a) set"
  assumes gen: "countably_generated_filter (uniformity :: ('a \<times> 'a) filter)"
  assumes conv: "\<And>(u :: nat \<Rightarrow> 'a). Cauchy u \<Longrightarrow> convergent u"
  assumes "cauchy_filter F"
  shows   "convergent_filter F"
proof -
  from gen obtain B :: "nat \<Rightarrow> ('a \<times> 'a) set" where B:
    "antimono B" "uniformity = (INF n. principal (B n))"
    "\<And>P. eventually P uniformity \<longleftrightarrow> (\<exists>i. \<forall>x\<in>B i. P x)"
    using countably_generated_filter_has_antimono_basis by blast

  show ?thesis
  proof (rule controlled_sequences_convergent_imp_complete_aux[where U = B])
    show "\<forall>\<^sub>F z in uniformity. z \<in> B n" for n
      unfolding B(3) by blast
  next
    fix f :: "nat \<Rightarrow> 'a"
    assume f: "\<And>N m n. N \<le> m \<Longrightarrow> N \<le> n \<Longrightarrow> (f m, f n) \<in> B N"
    have "Cauchy f" using f B
      by (intro controlled_seq_imp_Cauchy_seq[where U = B]) auto
    with conv show "convergent f"
      by simp
  qed fact+
qed

theorem (in uniform_space) Cauchy_seq_convergent_imp_complete:
  fixes U :: "nat \<Rightarrow> ('a \<times> 'a) set"
  assumes gen: "countably_generated_filter (uniformity :: ('a \<times> 'a) filter)"
  assumes conv: "\<And>(u :: nat \<Rightarrow> 'a). Cauchy u \<Longrightarrow> convergent u"
  shows   "class.complete_uniform_space open uniformity"
  by unfold_locales (use assms Cauchy_seq_convergent_imp_complete_aux in blast)

lemma (in metric_space) countably_generated_uniformity:
  "countably_generated_filter uniformity"
proof -
  have "(INF e\<in>{0<..}. principal {(x, y). dist (x::'a) y < e}) =
        (INF n\<in>UNIV. principal {(x, y). dist x y < 1 / real (Suc n)})" (is "?F = ?G")
    unfolding uniformity_dist
  proof (intro antisym)
    have "?G = (INF e\<in>(\<lambda>n. 1 / real (Suc n)) ` UNIV. principal {(x, y). dist x y < e})"
      by (simp add: image_image)
    also have "\<dots> \<ge> ?F"
      by (intro INF_superset_mono) auto
    finally show "?F \<le> ?G" .
  next
    show "?G \<le> ?F"
      unfolding le_filter_def
    proof safe
      fix P assume "eventually P ?F"
      then obtain \<epsilon> where \<epsilon>: "\<epsilon> > 0" "eventually P (principal {(x, y). dist x y < \<epsilon>})"
      proof (subst (asm) eventually_INF_base, goal_cases)
        case (2 \<epsilon>1 \<epsilon>2)
        thus ?case
          by (intro bexI[of _ "min \<epsilon>1 \<epsilon>2"]) auto
      qed auto
      from \<open>\<epsilon> > 0\<close> obtain n where "1 / real (Suc n) < \<epsilon>"
        using nat_approx_posE by blast
      then have "eventually P (principal {(x, y). dist x y < 1 / real (Suc n)})"
        using \<epsilon>(2) by (auto simp: eventually_principal)
      thus "eventually P ?G"
        by (intro eventually_INF1) auto
    qed
  qed
  thus "countably_generated_filter uniformity"
    unfolding countably_generated_filter_def uniformity_dist by fast
qed

subclass (in complete_space) complete_uniform_space
proof (rule Cauchy_seq_convergent_imp_complete)
  show "convergent f" if "Cauchy f" for f
    using Cauchy_convergent that by blast
qed (fact countably_generated_uniformity)

lemma (in complete_uniform_space) complete_UNIV_cuspace [intro]: "complete UNIV"
  unfolding complete_uniform using cauchy_filter_convergent
  by (auto simp: convergent_filter.simps)



lemma norm_infprod_le:
  assumes "(f has_setprod S) X"
  assumes "(g has_setprod T) X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> norm (f x) \<le> g x"
  shows   "norm S \<le> T"
proof (rule tendsto_le)
  show "((\<lambda>Y. norm (\<Prod>x\<in>Y. f x)) \<longlongrightarrow> norm S) (finite_subsets_at_top X)"
    using assms(1) unfolding has_setprod_def by (intro tendsto_norm)
  show "((\<lambda>Y. \<Prod>x\<in>Y. g x) \<longlongrightarrow> T) (finite_subsets_at_top X)"
    using assms(2) unfolding has_setprod_def .
  show "\<forall>\<^sub>F x in finite_subsets_at_top X. norm (prod f x) \<le> (\<Prod>x\<in>x. g x)"
    by (simp add: assms(3) eventually_finite_subsets_at_top_weakI subsetD sum_norm_le)
qed auto

(*
lemma multipliable_on_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{comm_monoid_mult, t2_space, uniform_space}\<close>
  assumes times_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x+y)\<close>
  assumes multipliableAB: "(\<lambda>(x,y). f x y) multipliable_on (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x) multipliable_on (B x)\<close>
  shows \<open>(\<lambda>x. infprod (f x) (B x)) multipliable_on A\<close>
*)



lemma multipliable_on_UNIV_nonneg_real_iff:
  assumes "\<And>n. f n \<ge> (0 :: real)"
  shows   "f multipliable_on UNIV \<longleftrightarrow> multipliable f"
  using assms by (auto intro: norm_multipliable_imp_multipliable_on multipliable_on_imp_multipliable)

lemma multipliable_on_imp_bounded_partial_sums:
  fixes f :: "_ \<Rightarrow> 'a :: {topological_comm_monoid_mult, linorder_topology}"
  assumes f: "f multipliable_on A"
  shows   "\<exists>C. eventually (\<lambda>X. prod f X \<le> C) (finite_subsets_at_top A)"
proof -
  from assms obtain S where S: "(prod f \<longlongrightarrow> S) (finite_subsets_at_top A)"
    unfolding multipliable_on_def has_setprod_def by blast
  show ?thesis
  proof (cases "\<exists>C. C > S")
    case True
    then obtain C where C: "C > S"
      by blast
    have "\<forall>\<^sub>F X in finite_subsets_at_top A. prod f X < C"
      using S C by (rule order_tendstoD(2))
    thus ?thesis
      by (meson eventually_mono nless_le)
  next
    case False thus ?thesis
      by (meson not_eventuallyD not_le_imp_less)
  qed
qed

lemma has_setprod_mono':
  fixes S S' :: "'a :: {linorder_topology, ordered_comm_monoid_mult, topological_comm_monoid_mult}"
  assumes f: "(f has_setprod S) A" "(f has_setprod S') B" 
     and AB: "A \<subseteq> B" "\<And>x. x \<in> B - A \<Longrightarrow> f x \<ge> 0"
  shows   "S \<le> S'"
  using AB has_setprod_mono_neutral[OF f] by fastforce


context
  assumes "SORT_CONSTRAINT('a :: {topological_comm_monoid_mult, order_topology,
             ordered_comm_monoid_mult, conditionally_complete_linorder})"
begin

text \<open>
  Any family of non-negative numbers with bounded partial sums is multipliable, and the sum
  is simply the supremum of the partial sums.
\<close>
lemma nonneg_bounded_partial_sums_imp_has_setprod_SUP:
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> (0::'a)"
      and bound:  "eventually (\<lambda>X. prod f X \<le> C) (finite_subsets_at_top A)"
  shows   "(f has_setprod (SUP X\<in>{X. X \<subseteq> A \<and> finite X}. prod f X)) A"
proof -
  from bound obtain X0
    where X0: "X0 \<subseteq> A" "finite X0" "\<And>X. X0 \<subseteq> X \<Longrightarrow> X \<subseteq> A \<Longrightarrow> finite X \<Longrightarrow> prod f X \<le> C"
    by (force simp: eventually_finite_subsets_at_top)
  have bound': "prod f X \<le> C" if "X \<subseteq> A" "finite X" for X
  proof -
    have "prod f X \<le> prod f (X \<union> X0)"
      using that X0 assms(1) by (intro sum_mono2) auto
    also have "\<dots> \<le> C"
      by (simp add: X0 that)
    finally show ?thesis .
  qed
  hence bdd: "bdd_above (prod f ` {X. X \<subseteq> A \<and> finite X})"
    by (auto simp: bdd_above_def)

  show ?thesis unfolding has_setprod_def
  proof (rule increasing_tendsto)
    show "\<forall>\<^sub>F X in finite_subsets_at_top A. prod f X \<le> Sup (prod f ` {X. X \<subseteq> A \<and> finite X})"
      by (intro eventually_finite_subsets_at_top_weakI cSUP_upper[OF _ bdd]) auto
  next
    fix y assume "y < Sup (prod f ` {X. X \<subseteq> A \<and> finite X})"
    then obtain X where X: "X \<subseteq> A" "finite X" "y < prod f X"
      by (subst (asm) less_cSUP_iff[OF _ bdd]) auto
    from X have "eventually (\<lambda>X'. X \<subseteq> X' \<and> X' \<subseteq> A \<and> finite X') (finite_subsets_at_top A)"
      by (auto simp: eventually_finite_subsets_at_top)
    thus "eventually (\<lambda>X'. y < prod f X') (finite_subsets_at_top A)"
    proof eventually_elim
      case (elim X')
      note \<open>y < prod f X\<close>
      also have "prod f X \<le> prod f X'"
        using nonneg elim by (intro sum_mono2) auto
      finally show ?case .
    qed
  qed
qed

lemma nonneg_bounded_partial_sums_imp_multipliable_on:
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> (0::'a)"
      and bound:  "eventually (\<lambda>X. prod f X \<le> C) (finite_subsets_at_top A)"
  shows   "f multipliable_on A"
  using nonneg_bounded_partial_sums_imp_has_setprod_SUP[OF assms] by (auto simp: multipliable_on_def)

end

context
  assumes "SORT_CONSTRAINT('a :: {topological_comm_monoid_mult, linorder_topology,
             ordered_comm_monoid_mult, conditionally_complete_linorder})"
begin

lemma multipliable_on_comparison_test:
  assumes "f multipliable_on A" and "\<And>x. x \<in> A \<Longrightarrow> g x \<le> f x" and "\<And>x. x \<in> A \<Longrightarrow> (0::'a) \<le> g x"
  shows   "g multipliable_on A"
proof -
  obtain C where C: "\<forall>\<^sub>F X in finite_subsets_at_top A. prod f X \<le> C"
    using assms(1) multipliable_on_imp_bounded_partial_sums by blast
  show ?thesis
  proof (rule nonneg_bounded_partial_sums_imp_multipliable_on)
    show "\<forall>\<^sub>F X in finite_subsets_at_top A. prod g X \<le> C"
      using C assms 
      unfolding eventually_finite_subsets_at_top
      by (smt (verit, ccfv_SIG) order_trans subsetD sum_mono)
  qed (use assms in auto)
qed

end



lemma multipliable_on_subset:
  fixes f :: "_ \<Rightarrow> 'a :: {uniform_topological_group_add, topological_comm_monoid_mult, ab_group_add, complete_uniform_space}"
  assumes "f multipliable_on A" "B \<subseteq> A"
  shows "f multipliable_on B"
  by (rule multipliable_on_subset_aux[OF _ _ assms]) (auto simp: uniformly_continuous_add)

lemma multipliable_on_union:
  fixes f :: "_ \<Rightarrow> 'a :: {uniform_topological_group_add, topological_comm_monoid_mult, ab_group_add, complete_uniform_space}"
  assumes "f multipliable_on A" "f multipliable_on B"
  shows "f multipliable_on (A \<union> B)"
proof -
  have "f multipliable_on (A \<union> (B - A))"
    by (meson Diff_disjoint Diff_subset assms multipliable_on_Un_disjoint multipliable_on_subset)
  also have "A \<union> (B - A) = A \<union> B"
    by blast
  finally show ?thesis .
qed

lemma multipliable_on_insert_iff:
  fixes f :: "_ \<Rightarrow> 'a :: {uniform_topological_group_add, topological_comm_monoid_mult, ab_group_add, complete_uniform_space}"
  shows "f multipliable_on insert x A \<longleftrightarrow> f multipliable_on A"
  using multipliable_on_union[of f A "{x}"] by (auto intro: multipliable_on_subset)

lemma has_setprod_finiteI: "finite A \<Longrightarrow> S = prod f A \<Longrightarrow> (f has_setprod S) A"
  by simp

lemma has_setprod_insert:
  fixes f :: "'a \<Rightarrow> 'b :: topological_comm_monoid_mult"
  assumes "x \<notin> A" and "(f has_setprod S) A"
  shows   "(f has_setprod (f x + S)) (insert x A)"
proof -
  have "(f has_setprod (f x + S)) ({x} \<union> A)"
    using assms by (intro has_setprod_Un_disjoint) (auto intro: has_setprod_finiteI)
  thus ?thesis by simp
qed

lemma infprod_insert:
  fixes f :: "_ \<Rightarrow> 'a :: {topological_comm_monoid_mult, t2_space}"
  assumes "f multipliable_on A" "a \<notin> A"
  shows   "infprod f (insert a A) = f a + infprod f A"
  by (meson assms has_setprod_insert infprodI multipliable_iff_has_setprod_infprod)

lemma has_setprod_SigmaD:
  fixes f :: "'b \<times> 'c \<Rightarrow> 'a :: {topological_comm_monoid_mult,t3_space}"
  assumes sum1: "(f has_setprod S) (Sigma A B)"
  assumes sum2: "\<And>x. x \<in> A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod g x) (B x)"
  shows   "(g has_setprod S) A"
  unfolding has_setprod_def tendsto_def eventually_finite_subsets_at_top
proof (safe, goal_cases)
  case (1 X)
  with nhds_closed[of S X] obtain X'
    where X': "S \<in> X'" "closed X'" "X' \<subseteq> X" "eventually (\<lambda>y. y \<in> X') (nhds S)" by blast
  from X'(4) obtain X'' where X'': "S \<in> X''" "open X''" "X'' \<subseteq> X'"
    by (auto simp: eventually_nhds)
  with sum1 obtain Y :: "('b \<times> 'c) set"
    where Y: "Y \<subseteq> Sigma A B" "finite Y"
             "\<And>Z. Y \<subseteq> Z \<Longrightarrow> Z \<subseteq> Sigma A B \<Longrightarrow> finite Z \<Longrightarrow> prod f Z \<in> X''"
    unfolding has_setprod_def tendsto_def eventually_finite_subsets_at_top by force
  define Y1 :: "'b set" where "Y1 = fst ` Y"
  from Y have Y1: "Y1 \<subseteq> A" by (auto simp: Y1_def)
  define Y2 :: "'b \<Rightarrow> 'c set" where "Y2 = (\<lambda>x. {y. (x, y) \<in> Y})"
  have Y2: "finite (Y2 x)" "Y2 x \<subseteq> B x" if "x \<in> A" for x
    using that Y(1,2) unfolding Y2_def
    by (force simp: image_iff intro: finite_subset[of _ "snd ` Y"])+

  show ?case
  proof (rule exI[of _ Y1], safe, goal_cases)
    case (3 Z)
    define H where "H = (INF x\<in>Z. filtercomap (\<lambda>p. p x) (finite_subsets_at_top (B x)))"
    
    have "prod g Z \<in> X'"
    proof (rule Lim_in_closed_set)
      show "closed X'" by fact
    next
      show "((\<lambda>B'. prod (\<lambda>x. prod (\<lambda>y. f (x, y)) (B' x)) Z) \<longlongrightarrow> prod g Z) H"
        unfolding H_def
      proof (intro tendsto_prod filterlim_INF')
        fix x assume x: "x \<in> Z"
        with 3 have "x \<in> A" by auto
        from sum2[OF this] have "(prod (\<lambda>y. f (x, y)) \<longlongrightarrow> g x) (finite_subsets_at_top (B x))"
          by (simp add: has_setprod_def)
        thus "((\<lambda>B'. prod (\<lambda>y. f (x, y)) (B' x)) \<longlongrightarrow> g x)
                 (filtercomap (\<lambda>p. p x) (finite_subsets_at_top (B x)))"
          by (rule filterlim_compose[OF _ filterlim_filtercomap])
      qed auto
    next
      show "\<forall>\<^sub>F h in H. prod (\<lambda>x. prod (\<lambda>y. f (x, y)) (h x)) Z \<in> X'"
        unfolding H_def
      proof (subst eventually_INF_finite[OF \<open>finite Z\<close>], rule exI, safe)
        fix x assume x: "x \<in> Z"
        hence x': "x \<in> A" using 3 by auto
        show "eventually (\<lambda>h. finite (h x) \<and> Y2 x \<subseteq> h x \<and> h x \<subseteq> B x)
                (filtercomap (\<lambda>p. p x) (finite_subsets_at_top (B x)))" using 3 Y2[OF x']
          by (intro eventually_filtercomapI)
             (auto simp: eventually_finite_subsets_at_top intro: exI[of _ "Y2 x"])
      next
        fix h
        assume *: "\<forall>x\<in>Z. finite (h x) \<and> Y2 x \<subseteq> h x \<and> h x \<subseteq> B x"
        hence "prod (\<lambda>x. prod (\<lambda>y. f (x, y)) (h x)) Z = prod f (Sigma Z h)"
          using \<open>finite Z\<close> by (subst prod.Sigma) auto
        also have "\<dots> \<in> X''"
          using * 3 Y(1,2) by (intro Y; force simp: Y1_def Y2_def)
        also have "X'' \<subseteq> X'" by fact
        finally show "prod (\<lambda>x. prod (\<lambda>y. f (x, y)) (h x)) Z \<in> X'" .
      qed
    next
      have "H = (INF x\<in>SIGMA x:Z. {X. finite X \<and> X \<subseteq> B x}.
                  principal {y. finite (y (fst x)) \<and> snd x \<subseteq> y (fst x) \<and> y (fst x) \<subseteq> B (fst x)})"
        unfolding H_def finite_subsets_at_top_def filtercomap_INF filtercomap_principal
        by (simp add: INF_Sigma)
      also have "\<dots> \<noteq> bot"
      proof (rule INF_filter_not_bot, subst INF_principal_finite, goal_cases)
        case (2 X)
        define H' where
          "H' = (\<Inter>x\<in>X. {y. finite (y (fst x)) \<and> snd x \<subseteq> y (fst x) \<and> y (fst x) \<subseteq> B (fst x)})"
        from 2 have "(\<lambda>x. \<Union>(y,Y)\<in>X. if x = y then Y else {}) \<in> H'"
          by (force split: if_splits simp: H'_def)
        hence "H' \<noteq> {}" by blast
        thus "principal H' \<noteq> bot" by (simp add: principal_eq_bot_iff)
      qed
      finally show "H \<noteq> bot" .
    qed
    also have "X' \<subseteq> X" by fact
    finally show "prod g Z \<in> X" .
  qed (insert Y(1,2), auto simp: Y1_def)
qed

lemma has_setprod_unique:
  fixes f :: "_ \<Rightarrow> 'a :: {topological_comm_monoid_mult, t2_space}"
  assumes "(f has_setprod x) A" "(f has_setprod y) A"
  shows "x = y"
  using assms unfolding has_setprod_def using tendsto_unique finite_subsets_at_top_neq_bot by blast

lemma has_setprod_SigmaI:
  fixes f :: "_ \<Rightarrow> 'a :: {topological_comm_monoid_mult, t3_space}"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod g x) (B x)"
  assumes g: "(g has_setprod S) A"
  assumes multipliable: "f multipliable_on Sigma A B"
  shows   "(f has_setprod S) (Sigma A B)"
  by (metis f g has_setprod_SigmaD has_setprod_infprod has_setprod_unique local.multipliable)

lemma multipliable_on_SigmaD1:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> 'a :: {complete_uniform_space, uniform_topological_group_add, ab_group_add, topological_comm_monoid_mult}"
  assumes f: "(\<lambda>(x,y). f x y) multipliable_on Sigma A B"
  assumes x: "x \<in> A"
  shows   "f x multipliable_on B x"
proof -
  have "(\<lambda>(x,y). f x y) multipliable_on Sigma {x} B"
    using f by (rule multipliable_on_subset) (use x in auto)
  also have "?this \<longleftrightarrow> ((\<lambda>y. f x y) \<circ> snd) multipliable_on Sigma {x} B"
    by (intro multipliable_on_cong) auto
  also have "\<dots> \<longleftrightarrow> (\<lambda>y. f x y) multipliable_on snd ` Sigma {x} B"
    by (intro multipliable_on_reindex [symmetric] inj_onI) auto
  also have "snd ` Sigma {x} B = B x"
    by (force simp: Sigma_def)
  finally show ?thesis .
qed

lemma has_setprod_swap:
  "(f has_setprod S) (A \<times> B) \<longleftrightarrow> ((\<lambda>(x,y). f (y,x)) has_setprod S) (B \<times> A)"
proof -
  have "bij_betw (\<lambda>(x,y). (y,x)) (B \<times> A) (A \<times> B)"
    by (rule bij_betwI[of _ _ _ "\<lambda>(x,y). (y,x)"]) auto
  from has_setprod_reindex_bij_betw[OF this, where f = f] show ?thesis
    by (simp add: case_prod_unfold)
qed


lemma multipliable_on_swap:
  "f multipliable_on (A \<times> B) \<longleftrightarrow> (\<lambda>(x,y). f (y,x)) multipliable_on (B \<times> A)"
  by (metis has_setprod_swap multipliable_on_def)

lemma has_setprod_cmult_right_iff:
  fixes c :: "'a :: {topological_semigroup_mult, field}"
  assumes "c \<noteq> 0"
  shows   "((\<lambda>x. c * f x) has_setprod S) A \<longleftrightarrow> (f has_setprod (S / c)) A"
  using has_setprod_cmult_right[of f A "S/c" c]
        has_setprod_cmult_right[of "\<lambda>x. c * f x" A S "inverse c"] assms
  by (auto simp: field_simps)

lemma has_setprod_cmult_left_iff:
  fixes c :: "'a :: {topological_semigroup_mult, field}"
  assumes "c \<noteq> 0"
  shows   "((\<lambda>x. f x * c) has_setprod S) A \<longleftrightarrow> (f has_setprod (S / c)) A"
  by (smt (verit, best) assms has_setprod_cmult_right_iff has_setprod_cong mult.commute)

lemma finite_nonzero_values_imp_multipliable_on:
  assumes "finite {x\<in>X. f x \<noteq> 0}"
  shows   "f multipliable_on X"
  by (smt (verit, del_insts) Diff_iff assms mem_Collect_eq multipliable_on_cong_neutral multipliable_on_finite)

lemma multipliable_on_of_int_iff:
  "(\<lambda>x::'a. of_int (f x) :: 'b :: real_normed_algebra_1) multipliable_on A \<longleftrightarrow> f multipliable_on A"
proof
  assume "f multipliable_on A"
  thus "(\<lambda>x. of_int (f x)) multipliable_on A"
    by (rule multipliable_on_homomorphism) auto
next
  assume "(\<lambda>x. of_int (f x) :: 'b) multipliable_on A"
  then obtain S where "((\<lambda>x. of_int (f x) :: 'b) has_setprod S) A"
    by (auto simp: multipliable_on_def)
  hence "(prod (\<lambda>x. of_int (f x) :: 'b) \<longlongrightarrow> S) (finite_subsets_at_top A)"
    unfolding has_setprod_def .
  moreover have "1/2 > (0 :: real)"
    by auto
  ultimately have "eventually (\<lambda>X. dist (prod (\<lambda>x. of_int (f x) :: 'b) X) S < 1/2)
                     (finite_subsets_at_top A)"
    unfolding tendsto_iff by blast
  then obtain X where X: "finite X" "X \<subseteq> A"
     "\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> dist (prod (\<lambda>x. of_int (f x)) Y) S < 1/2"
    unfolding eventually_finite_subsets_at_top by metis

  have "prod f Y = prod f X" if "finite Y" "X \<subseteq> Y" "Y \<subseteq> A" for Y
  proof -
    have "dist (prod (\<lambda>x. of_int (f x)) X) S < 1/2"
      by (intro X) auto
    moreover have "dist (prod (\<lambda>x. of_int (f x)) Y) S < 1/2"
      by (intro X that)
    ultimately have "dist (prod (\<lambda>x. of_int (f x)) X) (prod (\<lambda>x. of_int (f x) :: 'b) Y) <
                       1/2 + 1/2"
      using dist_triangle_less_add by blast
    thus ?thesis
      by (simp add: dist_norm flip: of_int_prod of_int_diff)
  qed
  then have "{x\<in>A. f x \<noteq> 0} \<subseteq> X"
    by (smt (verit) X finite_insert insert_iff mem_Collect_eq subset_eq prod.insert)
  with \<open>finite X\<close> have "finite {x\<in>A. f x \<noteq> 0}"
    using finite_subset by blast
  thus "f multipliable_on A"
    by (rule finite_nonzero_values_imp_multipliable_on)
qed

lemma multipliable_on_of_nat_iff:
  "(\<lambda>x::'a. of_nat (f x) :: 'b :: real_normed_algebra_1) multipliable_on A \<longleftrightarrow> f multipliable_on A"
proof
  assume "f multipliable_on A"
  thus "(\<lambda>x. of_nat (f x) :: 'b) multipliable_on A"
    by (rule multipliable_on_homomorphism) auto
next
  assume "(\<lambda>x. of_nat (f x) :: 'b) multipliable_on A"
  hence "(\<lambda>x. of_int (int (f x)) :: 'b) multipliable_on A"
    by simp
  also have "?this \<longleftrightarrow> (\<lambda>x. int (f x)) multipliable_on A"
    by (rule multipliable_on_of_int_iff)
  also have "\<dots> \<longleftrightarrow> f multipliable_on A"
    by (simp add: multipliable_on_discrete_iff)
  finally show "f multipliable_on A" .
qed

lemma infprod_of_nat:
  "infprod (\<lambda>x::'a. of_nat (f x) :: 'b :: {real_normed_algebra_1}) A = of_nat (infprod f A)"
  by (metis has_setprod_infprod has_setprod_of_nat infprodI infprod_def of_nat_0 multipliable_on_of_nat_iff)

lemma infprod_of_int:
  "infprod (\<lambda>x::'a. of_int (f x) :: 'b :: {real_normed_algebra_1}) A = of_int (infprod f A)"
  by (metis has_setprod_infprod has_setprod_of_int infprodI infprod_not_exists of_int_0 multipliable_on_of_int_iff)


lemma multipliable_on_SigmaI:
  fixes f :: "_ \<Rightarrow> 'a :: {linorder_topology, ordered_comm_monoid_mult, topological_comm_monoid_mult,
                          conditionally_complete_linorder}"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod g x) (B x)"
  assumes g: "g multipliable_on A"
  assumes f_nonneg: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> f (x, y) \<ge> (0 :: 'a)"
  shows   "f multipliable_on Sigma A B"
proof -
  have g_nonneg: "g x \<ge> 0" if "x \<in> A" for x
    using f by (rule has_setprod_nonneg) (use f_nonneg that in auto)
  obtain C where C: "eventually (\<lambda>X. prod g X \<le> C) (finite_subsets_at_top A)"
    using multipliable_on_imp_bounded_partial_sums[OF g] by blast

  have sum_g_le: "prod g X \<le> C" if X: "finite X" "X \<subseteq> A" for X
  proof -
    from C obtain X' where X':
      "finite X'" "X' \<subseteq> A" "\<And>Y. finite Y \<Longrightarrow> X' \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod g Y \<le> C"
      unfolding eventually_finite_subsets_at_top by metis
    have "prod g X \<le> prod g (X \<union> X')"
      using X X' by (intro sum_mono2 g_nonneg) auto
    also have "\<dots> \<le> C"
      using X X'(1,2) by (intro X'(3)) auto
    finally show ?thesis .
  qed

  have "prod f Y \<le> C" if Y: "finite Y" "Y \<subseteq> Sigma A B" for Y
  proof -
    define Y1 and Y2 where "Y1 = fst ` Y" and "Y2 = (\<lambda>x. snd ` {z\<in>Y. fst z = x})"
    have Y12: "Y = Sigma Y1 Y2"
      unfolding Y1_def Y2_def by force
    have [intro]: "finite Y1" "\<And>x. x \<in> Y1 \<Longrightarrow> finite (Y2 x)"
      using Y unfolding Y1_def Y2_def by auto
    have Y12_subset: "Y1 \<subseteq> A" "\<And>x. Y2 x \<subseteq> B x"
      using Y by (auto simp: Y1_def Y2_def)

    have "prod f Y = prod f (Sigma Y1 Y2)"
      by (simp add: Y12)
    also have "\<dots> = (\<Prod>x\<in>Y1. \<Prod>y\<in>Y2 x. f (x, y))"
      by (subst prod.Sigma) auto
    also have "\<dots> \<le> (\<Prod>x\<in>Y1. g x)"
    proof (rule sum_mono)
      fix x assume x: "x \<in> Y1"
      show "(\<Prod>y\<in>Y2 x. f (x, y)) \<le> g x"
      proof (rule has_setprod_mono')
        show "((\<lambda>y. f (x, y)) has_setprod (\<Prod>y\<in>Y2 x. f (x, y))) (Y2 x)"
          using x by (intro has_setprod_finite) auto
        show "((\<lambda>y. f (x, y)) has_setprod g x) (B x)"
          by (rule f) (use x Y12_subset in auto)
        show "f (x, y) \<ge> 0" if "y \<in> B x - Y2 x" for y
          using x that Y12_subset by (intro f_nonneg) auto
      qed (use Y12_subset in auto)
    qed
    also have "\<dots> \<le> C"
      using Y12_subset by (intro sum_g_le) auto
    finally show ?thesis .
  qed

  hence "\<forall>\<^sub>F X in finite_subsets_at_top (Sigma A B). prod f X \<le> C"
    unfolding eventually_finite_subsets_at_top by auto
  thus ?thesis
    by (metis SigmaE f_nonneg nonneg_bounded_partial_sums_imp_multipliable_on)
qed

lemma multipliable_on_UnionI:
  fixes f :: "_ \<Rightarrow> 'a :: {linorder_topology, ordered_comm_monoid_mult, topological_comm_monoid_mult,
                          conditionally_complete_linorder}"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> (f has_setprod g x) (B x)"
  assumes g: "g multipliable_on A"
  assumes f_nonneg: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> f y \<ge> (0 :: 'a)"
  assumes disj: "disjoint_family_on B A"
  shows   "f multipliable_on (\<Union>x\<in>A. B x)"
proof -
  have "f \<circ> snd multipliable_on Sigma A B"
    using assms by (intro multipliable_on_SigmaI[where g = g]) auto
  also have "?this \<longleftrightarrow> f multipliable_on (snd ` Sigma A B)" using assms
    by (subst multipliable_on_reindex; force simp: disjoint_family_on_def inj_on_def)
  also have "snd ` (Sigma A B) = (\<Union>x\<in>A. B x)"
    by force
  finally show ?thesis .
qed

lemma multipliable_on_SigmaD:
  fixes f :: "'a \<times> 'b \<Rightarrow> 'c :: {topological_comm_monoid_mult,t3_space}"
  assumes sum1: "f multipliable_on (Sigma A B)"
  assumes sum2: "\<And>x. x \<in> A \<Longrightarrow> (\<lambda>y. f (x, y)) multipliable_on (B x)"
  shows   "(\<lambda>x. infprod (\<lambda>y. f (x, y)) (B x)) multipliable_on A"
  using assms unfolding multipliable_on_def
  by (smt (verit, del_insts) assms has_setprod_SigmaD has_setprod_cong has_setprod_infprod)

lemma multipliable_on_UnionD:
  fixes f :: "'a \<Rightarrow> 'c :: {topological_comm_monoid_mult,t3_space}"
  assumes sum1: "f multipliable_on (\<Union>x\<in>A. B x)"
  assumes sum2: "\<And>x. x \<in> A \<Longrightarrow> f multipliable_on (B x)"
  assumes disj: "disjoint_family_on B A"
  shows   "(\<lambda>x. infprod f (B x)) multipliable_on A"
proof -
  have "(\<Union>x\<in>A. B x) = snd ` Sigma A B"
    by (force simp: Sigma_def)
  with sum1 have "f multipliable_on (snd ` Sigma A B)"
    by simp
  also have "?this \<longleftrightarrow> (f \<circ> snd) multipliable_on (Sigma A B)"
    using disj by (intro multipliable_on_reindex inj_onI) (force simp: disjoint_family_on_def)
  finally show "(\<lambda>x. infprod f (B x)) multipliable_on A"
    using multipliable_on_SigmaD[of "f \<circ> snd" A B] sum2 by simp
qed

lemma multipliable_on_Union_iff:
  fixes f :: "_ \<Rightarrow> 'a :: {linorder_topology, ordered_comm_monoid_mult, topological_comm_monoid_mult,
                          conditionally_complete_linorder, t3_space}"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> (f has_setprod g x) (B x)"
  assumes f_nonneg: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> f y \<ge> 0"
  assumes disj: "disjoint_family_on B A"
  shows   "f multipliable_on (\<Union>x\<in>A. B x) \<longleftrightarrow> g multipliable_on A"
proof
  assume "g multipliable_on A"
  thus "f multipliable_on (\<Union>x\<in>A. B x)"
    using multipliable_on_UnionI[of A f B g] assms by auto
next
  assume "f multipliable_on (\<Union>x\<in>A. B x)"
  hence "(\<lambda>x. infprod f (B x)) multipliable_on A"
    using assms by (intro multipliable_on_UnionD) (auto dest: has_setprod_imp_multipliable)
  also have "?this \<longleftrightarrow> g multipliable_on A"
    using assms by (intro multipliable_on_cong) (auto simp: infprodI)
  finally show "g multipliable_on A" .
qed

lemma has_setprod_Sigma':
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{comm_monoid_mult,uniform_space,uniform_topological_group_add}\<close>
  assumes multipliableAB: "(f has_setprod a) (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod (b x)) (B x)\<close>
  shows "(b has_setprod a) A"
  by (intro has_setprod_Sigma[OF _ assms] uniformly_continuous_add)

lemma abs_multipliable_on_comparison_test':
  assumes "g multipliable_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (f x) \<le> g x"
  shows   "(\<lambda>x. norm (f x)) multipliable_on A"
proof (rule Infinite_Sum.abs_multipliable_on_comparison_test)
  have "g multipliable_on A \<longleftrightarrow> (\<lambda>x. norm (g x)) multipliable_on A"
    by (metis multipliable_on_iff_abs_multipliable_on_real)
  with assms show "(\<lambda>x. norm (g x)) multipliable_on A" by blast
qed (use assms in fastforce)

lemma has_setprod_geometric_from_1:
  fixes z :: "'a :: {real_normed_field, banach}"
  assumes "norm z < 1"
  shows   "((\<lambda>n. z ^ n) has_setprod (z / (1 - z))) {1..}"
proof -
  have [simp]: "z \<noteq> 1"
    using assms by auto
  have "(\<lambda>n. z ^ Suc n) sums (1 / (1 - z) - 1)"
    using geometric_sums[of z] assms by (subst sums_Suc_iff) auto
  also have "1 / (1 - z) - 1 = z / (1 - z)"
    by (auto simp: field_simps)
  finally have "(\<lambda>n. z ^ Suc n) sums (z / (1 - z))" .
  moreover have "multipliable (\<lambda>n. norm (z ^ Suc n))"
    using assms
    by (subst multipliable_Suc_iff) (auto simp: norm_power intro!: multipliable_geometric)
  ultimately have "((\<lambda>n. z ^ Suc n) has_setprod (z / (1 - z))) UNIV"
    by (intro norm_multipliable_imp_has_setprod)
  also have "?this \<longleftrightarrow> ?thesis"
    by (intro has_setprod_reindex_bij_witness[of _ "\<lambda>n. n-1" "\<lambda>n. n+1"]) auto
  finally show ?thesis .
qed 

lemma has_setprod_divide_const:
  fixes f :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, field, semiring_0}"
  shows "(f has_setprod S) A \<Longrightarrow> ((\<lambda>x. f x / c) has_setprod (S / c)) A"
  using has_setprod_cmult_right[of f A S "inverse c"] by (simp add: field_simps)

lemma has_setprod_uminusI:
  fixes f :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, ring_1}"
  shows "(f has_setprod S) A \<Longrightarrow> ((\<lambda>x. -f x) has_setprod (-S)) A"
  using has_setprod_cmult_right[of f A S "-1"] by simp

*)

end
