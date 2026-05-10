theory Infinite_Product
  imports "HOL-Complex_Analysis.Complex_Analysis"
    "HOL-ex.Sketch_and_Explore" Isar_Explore

begin

no_notation Infinite_Set_Sum.abs_summable_on (infix \<open>abs'_summable'_on\<close> 50)

(*REPLACE*)
lemma tendsto_divide [tendsto_intros]:
  fixes a b :: "'a::real_normed_div_algebra"
  shows "(f \<longlongrightarrow> a) F \<Longrightarrow> (g \<longlongrightarrow> b) F \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> ((\<lambda>x. f x / g x) \<longlongrightarrow> a / b) F"
  by (simp add: tendsto_mult tendsto_inverse divide_inverse)

(* TODO Move *)
lemma filterlim_map_prod:
  assumes "filterlim f F F'" "filterlim g G G'"
  shows   "filterlim (map_prod f g) (F \<times>\<^sub>F G) (F' \<times>\<^sub>F G')"
  unfolding map_prod_def case_prod_unfold
  by (intro filterlim_Pair filterlim_compose[OF _ filterlim_fst] filterlim_compose[OF _ filterlim_snd] assms)


definition HAS_SETPROD :: \<open>('a \<Rightarrow> 'b :: {semidom, topological_semigroup_mult, t2_space}) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool\<close> 
    where has_setprod_def: \<open>HAS_SETPROD f A x \<longleftrightarrow> (prod f \<longlongrightarrow> x) (finite_subsets_at_top A)\<close>

abbreviation has_setprod (infixr "has'_setprod" 46) where
  "(f has_setprod S) A \<equiv> HAS_SETPROD f A S"
                                                                    
definition multipliable_on :: "('a \<Rightarrow> 'b::{semidom, topological_semigroup_mult, t2_space}) \<Rightarrow> 'a set \<Rightarrow> bool" (infixr "multipliable'_on" 46) where
  "f multipliable_on A \<equiv> (\<exists>x. (f has_setprod x) A)"

(*
  TODO from Manuel: I introduced this more robust notion of multipliability akin to "convergent_prod" for
  products of sequences. It does not allow convergence to 0 and is more well-behaved in some cases.
*)
definition strongly_multipliable_on :: "('a \<Rightarrow> 'b::{semidom, topological_semigroup_mult, t2_space}) \<Rightarrow> 'a set \<Rightarrow> bool" (infixr "strongly'_multipliable'_on" 46) where
  "f strongly_multipliable_on A \<equiv> finite {x\<in>A. f x = 0} \<and> (\<exists>P. (f has_setprod P) {x\<in>A. f x \<noteq> 0} \<and> P \<noteq> 0)"

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

lemma has_setprod_imp_multipliable: "(f has_setprod S) A \<Longrightarrow> f multipliable_on A"
  by (auto simp: multipliable_on_def)

lemma has_setprodI:
  assumes "((\<lambda>X. \<Prod>x\<in>X. f x) \<longlongrightarrow> P) (finite_subsets_at_top A)"
  shows   "(f has_setprod P) A"
  using assms unfolding has_setprod_def .

lemma has_setprodD:
  assumes "(f has_setprod P) A"
  shows   "((\<lambda>X. \<Prod>x\<in>X. f x) \<longlongrightarrow> P) (finite_subsets_at_top A)"
  using assms unfolding has_setprod_def .

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

lemma abs_multipliable_on_cong_neutral: 
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 1\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 1\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows "f abs_multipliable_on S \<longleftrightarrow> g abs_multipliable_on T"
  unfolding abs_multipliable_on_def by (intro multipliable_on_cong_neutral) (use assms in auto)

lemma abs_multipliable_on_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "f abs_multipliable_on A \<longleftrightarrow> g abs_multipliable_on A"
  unfolding abs_multipliable_on_def by (intro multipliable_on_cong) (use assms in auto)

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

lemma abs_multipliable_on_finite[simp]:
  assumes "finite F"
  shows "f abs_multipliable_on F"
  unfolding abs_multipliable_on_def using assms by simp

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
proof -
  define g where "g x = 1 + norm (f x - 1)" for x
  from assms obtain L where lim: "(prod g \<longlongrightarrow> L) (finite_subsets_at_top A)"
    unfolding abs_multipliable_on_def multipliable_on_def has_setprod_def g_def by blast
  have g_ge: "g x \<ge> 1" for x
    unfolding g_def by auto
  have g_ge0: "g x \<ge> 0" for x
    using g_ge[of x] by linarith
  have norm_f_le_g: "norm (f x) \<le> g x" for x
  proof -
    have "norm (f x) = norm (1 + (f x - 1))" by simp
    also have "\<dots> \<le> norm (1::'b) + norm (f x - 1)" by (rule norm_triangle_ineq)
    also have "\<dots> = 1 + norm (f x - 1)" by simp
    also have "\<dots> = g x" unfolding g_def ..
    finally show ?thesis .
  qed
  have norm_prod_le_prod_g: "norm (prod f F) \<le> prod g F" if "finite F" for F
  proof -
    have "norm (prod f F) = prod (\<lambda>x. norm (f x)) F"
      by (simp add: prod_norm)
    also have "\<dots> \<le> prod g F"
      by (intro prod_mono conjI norm_f_le_g ballI) auto
    finally show ?thesis .
  qed
  have prod_g_nonneg: "prod g F \<ge> 0" if "finite F" for F
    by (intro prod_nonneg ballI) (use g_ge0 in auto)
  have dist_le: "dist (prod f F1) (prod f F2) \<le> dist (prod g F1) (prod g F2)"
    if F12: "F2 \<subseteq> F1" "finite F1" "F1 \<subseteq> A" for F1 F2
  proof -
    from F12 have finF2: "finite F2" using finite_subset by blast
    have "prod f F1 = prod f (F1 - F2) * prod f F2"
      using prod.subset_diff[OF F12(1,2)] by (simp add: mult.commute)
    hence eq1: "prod f F1 - prod f F2 = (prod f (F1 - F2) - 1) * prod f F2"
      by (simp add: algebra_simps)
    have "prod g F1 = prod g (F1 - F2) * prod g F2"
      using prod.subset_diff[OF F12(1,2)] by (simp add: mult.commute)
    hence eq2: "prod g F1 - prod g F2 = (prod g (F1 - F2) - 1) * prod g F2"
      by (simp add: algebra_simps)
    have key1: "norm (prod f (F1 - F2) - 1) \<le> prod g (F1 - F2) - 1"
    proof -
      have aux: "norm ((\<Prod>x\<in>S. f x) - 1) \<le> (\<Prod>x\<in>S. g x) - 1" if "finite S" for S
        using that
      proof (induction S)
        case empty
        then show ?case by simp
      next
        case (insert x S)
        have "norm ((\<Prod>y\<in>insert x S. f y) - 1) = norm (f x * prod f S - 1)"
          using insert.hyps by simp
        also have "\<dots> = norm ((f x - 1) * prod f S + (prod f S - 1))"
          by (simp add: algebra_simps)
        also have "\<dots> \<le> norm ((f x - 1) * prod f S) + norm (prod f S - 1)"
          by (rule norm_triangle_ineq)
        also have "\<dots> = norm (f x - 1) * norm (prod f S) + norm (prod f S - 1)"
          by (simp add: norm_mult)
        also have "\<dots> \<le> norm (f x - 1) * prod g S + (prod g S - 1)"
        proof (intro add_mono mult_left_mono)
          show "norm (prod f S) \<le> prod g S"
            using insert.hyps by (intro norm_prod_le_prod_g) auto
          show "norm (prod f S - 1) \<le> prod g S - 1"
            using insert.IH by simp
        qed auto
        also have "\<dots> = (1 + norm (f x - 1)) * prod g S - 1"
          by (simp add: algebra_simps)
        also have "\<dots> = g x * prod g S - 1"
          unfolding g_def ..
        also have "g x * prod g S = (\<Prod>y\<in>insert x S. g y)"
          using insert.hyps by simp
        finally show ?case by simp
      qed
      thus ?thesis
        using F12(2) by (auto intro: finite_Diff)
    qed
    have key2: "norm (prod f F2) \<le> prod g F2"
      using finF2 by (rule norm_prod_le_prod_g)
    have g_diff_ge1: "prod g (F1 - F2) \<ge> 1"
      by (meson DiffD1 F12(2) finite_Diff g_ge prod_ge_1)
    have g_F2_ge0: "prod g F2 \<ge> 0"
      using finF2 by (rule prod_g_nonneg)
    have "norm (prod f F1 - prod f F2) = norm ((prod f (F1 - F2) - 1) * prod f F2)"
      by (simp add: eq1)
    also have "\<dots> = norm (prod f (F1 - F2) - 1) * norm (prod f F2)"
      by (rule norm_mult)
    also have "\<dots> \<le> (prod g (F1 - F2) - 1) * prod g F2"
      by (intro mult_mono key1 key2 norm_ge_zero) (use g_diff_ge1 in linarith)
    also have "\<dots> = prod g F1 - prod g F2"
      using eq2 by simp
    also have "\<dots> \<le> \<bar>prod g F1 - prod g F2\<bar>"
      by linarith
    also have "\<dots> = dist (prod g F1) (prod g F2)"
      unfolding dist_real_def ..
    finally show ?thesis unfolding dist_norm .
  qed
  \<comment> \<open>The absolute product is Cauchy, so the original product is too\<close>
  have cauchy_f: "cauchy_filter (filtermap (prod f) (finite_subsets_at_top A))"
    unfolding cauchy_filter_metric_filtermap
  proof (intro allI impI)
    fix e :: real assume "e > 0"
    \<comment> \<open>Since prod g converges to L, it is Cauchy\<close>
    from lim have cauchy_g: "cauchy_filter (filtermap (prod g) (finite_subsets_at_top A))"
      by (auto intro!: nhds_imp_cauchy_filter simp: filterlim_def)
    define d where "d = e / 2"
    have "d > 0" using \<open>e > 0\<close> unfolding d_def by simp
    have "\<exists>P. eventually P (finite_subsets_at_top A) \<and>
              (\<forall>x y. P x \<and> P y \<longrightarrow> dist (prod g x) (prod g y) < d)"
      using cauchy_g \<open>d > 0\<close> by (simp add: cauchy_filter_metric_filtermap)
    then obtain P where ev_P: "eventually P (finite_subsets_at_top A)"
      and P_close: "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> dist (prod g x) (prod g y) < d"
      by blast
    from ev_P obtain F0 where F0: "finite F0" "F0 \<subseteq> A"
      and F0_P: "\<And>F. finite F \<Longrightarrow> F0 \<subseteq> F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> P F"
      unfolding eventually_finite_subsets_at_top by metis
    define Q where "Q F \<longleftrightarrow> finite F \<and> F0 \<subseteq> F \<and> F \<subseteq> A" for F
    have ev_Q: "eventually Q (finite_subsets_at_top A)"
      unfolding Q_def eventually_finite_subsets_at_top using F0 by blast
    have "dist (prod f x) (prod f y) < e" if "Q x" "Q y" for x y
    proof -
      define F where "F = x \<union> y"
      have F_fin: "finite F" and F_sub: "F \<subseteq> A" and x_sub: "x \<subseteq> F" and y_sub: "y \<subseteq> F"
        using that unfolding F_def Q_def by auto
      have F0_sub_F: "F0 \<subseteq> F" using that unfolding F_def Q_def by auto
      have "P F" using F0_P F_fin F0_sub_F F_sub by auto
      have "P x" using F0_P that unfolding Q_def by auto
      have "P y" using F0_P that unfolding Q_def by auto
      have fx_le: "dist (prod f F) (prod f x) \<le> dist (prod g F) (prod g x)"
        using dist_le[of x F] x_sub F_fin F_sub by auto
      have fy_le: "dist (prod f F) (prod f y) \<le> dist (prod g F) (prod g y)"
        using dist_le[of y F] y_sub F_fin F_sub by auto
      have gx_lt: "dist (prod g F) (prod g x) < d"
        using P_close[OF \<open>P F\<close> \<open>P x\<close>] .
      have gy_lt: "dist (prod g F) (prod g y) < d"
        using P_close[OF \<open>P F\<close> \<open>P y\<close>] .
      have "dist (prod f x) (prod f y) \<le> dist (prod f F) (prod f x) + dist (prod f F) (prod f y)"
        by (rule dist_triangle3)
      also have "\<dots> \<le> dist (prod g F) (prod g x) + dist (prod g F) (prod g y)"
        by (intro add_mono fx_le fy_le)
      also have "\<dots> < d + d"
        by (intro add_strict_mono gx_lt gy_lt)
      also have "\<dots> = e" unfolding d_def by simp
      finally show ?thesis .
    qed
    thus "\<exists>P. eventually P (finite_subsets_at_top A) \<and>
              (\<forall>x y. P x \<and> P y \<longrightarrow> dist (prod f x) (prod f y) < e)"
      using ev_Q by blast
  qed
  moreover have "complete (UNIV :: 'b set)"
    using Cauchy_convergent complete_def convergent_def by blast
  ultimately obtain L' where "(prod f \<longlongrightarrow> L') (finite_subsets_at_top A)"
    using cauchy_filter_complete_converges[of "filtermap (prod f) (finite_subsets_at_top A)" UNIV]
    by (auto simp: filterlim_def filtermap_bot_iff)
  thus ?thesis
    unfolding multipliable_on_def has_setprod_def by blast
qed

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

lemma abs_multipliable_on_Un_disjoint:
  fixes f g :: "'a \<Rightarrow> 'b :: real_normed_algebra_1"
  assumes "f abs_multipliable_on A"
  assumes "f abs_multipliable_on B"
  assumes disj: "A \<inter> B = {}"
  shows \<open>f abs_multipliable_on (A \<union> B)\<close>
  using assms unfolding abs_multipliable_on_def by (intro multipliable_on_Un_disjoint)

lemma infprod_Un_disjoint:
  fixes f g :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, field, t2_space}"
  assumes "f multipliable_on A"
  assumes "f multipliable_on B"
  assumes disj: "A \<inter> B = {}"
  shows \<open>infprod f (A \<union> B) = infprod f A * infprod f B\<close>
  by (intro infprodI has_setprod_Un_disjoint has_setprod_infprod assms)  

lemma abs_convergent_prod_imp_setprod:
  fixes f :: "nat \<Rightarrow> 'b :: real_normed_field"
  assumes "abs_convergent_prod f" and "f has_prod P"
  shows   "(f has_setprod P) (UNIV :: nat set)"
proof (rule has_setprodI, unfold tendsto_iff, intro allI impI)
  fix e :: real assume \<open>e > 0\<close>
  from assms(2) have seq_lim: \<open>(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> P\<close>
    by (rule has_prod_imp_tendsto)
  from assms(1) have ev_nz: \<open>\<forall>\<^sub>F n in sequentially. f n \<noteq> 0\<close>
    by (rule abs_convergent_prod_imp_ev_nonzero)
  then obtain N0 where N0: \<open>\<And>n. n \<ge> N0 \<Longrightarrow> f n \<noteq> 0\<close>
    by (auto simp: eventually_at_top_linorder)

  \<comment> \<open>The absolute product converges sequentially\<close>
  define g where \<open>g n = 1 + norm (f n - 1)\<close> for n
  from assms(1)[unfolded abs_convergent_prod_def]
  have abs_conv: \<open>convergent_prod g\<close> unfolding g_def .
  have g_nz: \<open>g n \<noteq> 0\<close> for n
    unfolding g_def by (metis le_add_same_cancel1 norm_ge_zero not_one_le_zero)
  then obtain L_abs where L_abs: \<open>g has_prod L_abs\<close> and \<open>L_abs \<noteq> 0\<close>
    using abs_conv convergent_prod_has_prod prodinf_nonzero by blast
  have g_ge1: \<open>g n \<ge> 1\<close> for n unfolding g_def by auto
  have g_ge0: \<open>g n \<ge> 0\<close> for n using g_ge1[of n] by linarith

  \<comment> \<open>Sequential partial products of g converge to L_abs\<close>
  from L_abs have g_seq: \<open>(\<lambda>n. prod g {..n}) \<longlonglongrightarrow> L_abs\<close>
    by (rule has_prod_imp_tendsto)

  \<comment> \<open>Bound: for any finite S, norm(prod f S - 1) \<le> prod g S - 1\<close>
  have norm_bound: \<open>norm ((\<Prod>n\<in>S. f n) - 1) \<le> (\<Prod>n\<in>S. g n) - 1\<close>
    if \<open>finite S\<close> for S :: \<open>nat set\<close>
    using norm_prod_minus1_le_prod_minus1[of \<open>\<lambda>n. f n - 1\<close> S] by (simp add: g_def)

  \<comment> \<open>Bound: for any finite S, norm(prod f S) \<le> prod g S\<close>
  have norm_prod_bound: \<open>norm (prod f S) \<le> prod g S\<close>
    if \<open>finite S\<close> for S :: \<open>nat set\<close>
    using that
  proof induction
    case empty
    then show ?case by auto
  next
    case (insert n S)
    then show ?case
      by (metis (no_types, lifting) prod_norm g_def prod_mono norm_ge_zero norm_one norm_triangle_sub)
  qed

  \<comment> \<open>For finite S \<subseteq> {N+1,...}, prod g S \<le> prod g {..Max S} / prod g {..N}\<close>
  \<comment> \<open>which is bounded by L_abs / prod g {..N}\<close>
  \<comment> \<open>and prod g {..N} \<rightarrow> L_abs, so the tail \<rightarrow> 1\<close>

  \<comment> \<open>Partial products of g are bounded by L_abs (monotone increasing \<rightarrow> limit)\<close>
  have g_partial_le: \<open>prod g {..n} \<le> L_abs\<close> for n
  proof (rule ccontr)
    assume \<open>\<not> prod g {..n} \<le> L_abs\<close>
    then have gt: \<open>prod g {..n} > L_abs\<close> by simp
    define e' where \<open>e' = prod g {..n} - L_abs\<close>
    have \<open>e' > 0\<close> using gt by (simp add: e'_def)
    from g_seq[unfolded tendsto_iff, rule_format, OF this]
    obtain N' where N': \<open>\<And>m. m \<ge> N' \<Longrightarrow> dist (prod g {..m}) L_abs < e'\<close>
      by (auto simp: eventually_at_top_linorder)
    have \<open>prod g {..n} \<le> prod g {..max n N'}\<close>
      by (intro prod_mono2) (use g_ge1 g_ge0 in auto)
    hence \<open>dist (prod g {..max n N'}) L_abs \<ge> e'\<close>
      using gt by (simp add: dist_real_def e'_def)
    moreover have \<open>dist (prod g {..max n N'}) L_abs < e'\<close>
      using N'[of \<open>max n N'\<close>] by simp
    ultimately show False by linarith
  qed

  show \<open>\<forall>\<^sub>F x in finite_subsets_at_top (UNIV :: nat set). dist (prod f x) P < e\<close>
  proof -
    \<comment> \<open>Choose N so that sequential partial products are within e/2 of P\<close>
    from seq_lim[unfolded tendsto_iff, rule_format, OF half_gt_zero[OF \<open>e > 0\<close>]]
    obtain N1 where N1: \<open>\<And>n. n \<ge> N1 \<Longrightarrow> dist (prod f {..n}) P < e/2\<close>
      by (auto simp: eventually_at_top_linorder)
    \<comment> \<open>Choose N so that the absolute product tail is within e/2 of L_abs\<close>
    from g_seq[unfolded tendsto_iff, rule_format, OF half_gt_zero[OF \<open>e > 0\<close>]]
    obtain N2 where N2: \<open>\<And>n. n \<ge> N2 \<Longrightarrow> dist (prod g {..n}) L_abs < e/2\<close>
      by (auto simp: eventually_at_top_linorder)
    define N where \<open>N = max N1 N2\<close>
    \<comment> \<open>The witness set is {..N}\<close>
    show ?thesis
      unfolding eventually_finite_subsets_at_top
    proof (intro exI conjI allI impI)
      show \<open>finite {..N}\<close> by simp
      show \<open>{..N} \<subseteq> (UNIV :: nat set)\<close> by simp
    next
      fix Y :: \<open>nat set\<close>
      assume Y: \<open>finite Y \<and> {..N} \<subseteq> Y \<and> Y \<subseteq> UNIV\<close>
      then have finY: \<open>finite Y\<close> and NY: \<open>{..N} \<subseteq> Y\<close> by auto
      define M where \<open>M = Max Y\<close>
      have \<open>Y \<noteq> {}\<close> using NY by auto
      then have MMax: \<open>M = Max Y\<close> and MY: \<open>Y \<subseteq> {..M}\<close> and MN: \<open>M \<ge> N\<close>
        using finY NY by (auto simp: M_def intro: Max_ge subset_iff[THEN iffD2])
      have finM: \<open>finite {..M}\<close> by simp
      \<comment> \<open>Factoring: prod f {..M} = prod f ({..M} - Y) * prod f Y\<close>
      have factor_f: \<open>prod f {..M} = prod f ({..M} - Y) * prod f Y\<close>
        using prod.subset_diff[OF MY finM, of f] .
      have factor_g: \<open>prod g {..M} = prod g ({..M} - Y) * prod g Y\<close>
        using prod.subset_diff[OF MY finM, of g] .
      \<comment> \<open>Key bound: dist(prod f Y, prod f {..M}) \<le> L_abs - prod g {..N}\<close>
      have dist_bound: \<open>dist (prod f Y) (prod f {..M}) \<le> L_abs - prod g {..N}\<close>
      proof -
        have \<open>dist (prod f Y) (prod f {..M}) = norm (prod f Y - prod f {..M})\<close>
          by (simp add: dist_norm)
        also have \<open>\<dots> = norm (prod f Y - prod f ({..M} - Y) * prod f Y)\<close>
          by (simp add: factor_f mult.commute)
        also have \<open>\<dots> = norm (prod f Y * (1 - prod f ({..M} - Y)))\<close>
          by (simp add: algebra_simps)
        also have \<open>\<dots> = norm (prod f Y) * norm (1 - prod f ({..M} - Y))\<close>
          by (simp add: norm_mult)
        also have \<open>\<dots> = norm (prod f Y) * norm (prod f ({..M} - Y) - 1)\<close>
          by (metis norm_minus_commute)
        also have \<open>\<dots> \<le> prod g Y * (prod g ({..M} - Y) - 1)\<close>
        proof (intro mult_mono)
          show \<open>norm (prod f Y) \<le> prod g Y\<close>
            using norm_prod_bound[OF finY] .
          show \<open>norm (prod f ({..M} - Y) - 1) \<le> prod g ({..M} - Y) - 1\<close>
            using norm_bound[of \<open>{..M} - Y\<close>] finM finite_Diff by blast
          show \<open>0 \<le> norm (prod f ({..M} - Y) - 1)\<close> by simp
          show \<open>0 \<le> prod g Y\<close>
            by (intro prod_nonneg) (use g_ge0 in auto)
        qed
        also have \<open>\<dots> = prod g {..M} - prod g Y\<close>
          using factor_g by (simp add: algebra_simps)
        also have \<open>\<dots> \<le> prod g {..M} - prod g {..N}\<close>
        proof -
          have \<open>prod g {..N} \<le> prod g Y\<close>
            by (intro prod_mono2 finY) (use NY g_ge1 g_ge0 in auto)
          thus ?thesis by linarith
        qed
        also have \<open>\<dots> \<le> L_abs - prod g {..N}\<close>
        proof -
          have \<open>prod g {..M} \<le> L_abs\<close>
          using g_partial_le .
          thus ?thesis by linarith
        qed
        finally show ?thesis .
      qed
      \<comment> \<open>The absolute product tail bound is < e/2\<close>
      have tail_bound: \<open>L_abs - prod g {..N} < e/2\<close>
      proof -
        have \<open>dist (prod g {..N}) L_abs < e/2\<close>
          using N2[of N] by (auto simp: N_def)
        moreover have \<open>prod g {..N} \<le> L_abs\<close>
          using g_partial_le .
        ultimately show ?thesis by (simp add: dist_real_def)
      qed
      \<comment> \<open>Sequential bound: dist(prod f {..M}, P) < e/2\<close>
      have seq_bound: \<open>dist (prod f {..M}) P < e/2\<close>
        using N1[of M] MN by (auto simp: N_def)
      \<comment> \<open>Combine\<close>
      have \<open>dist (prod f Y) P \<le> dist (prod f Y) (prod f {..M}) + dist (prod f {..M}) P\<close>
        by (rule dist_triangle)
      also have \<open>\<dots> < (L_abs - prod g {..N}) + e/2\<close>
        using dist_bound seq_bound by linarith
      also have \<open>\<dots> < e/2 + e/2\<close> using tail_bound by linarith
      also have \<open>\<dots> = e\<close> by simp
      finally show \<open>dist (prod f Y) P < e\<close> .
    qed
  qed
qed


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

(*
  Specialised to real_normed_field following Manuel's advice.
  The proof uses the Cauchy filter approach: since the partial products over A converge,
  those over B form a Cauchy net (by dividing out the fixed finite product over F0 \<inter> (A-B)),
  which converges by completeness.
*)
lemma multipliable_on_subset_aux:
  fixes A B and f :: \<open>'a \<Rightarrow> 'b::real_normed_field\<close>
  assumes complete: \<open>complete (UNIV :: 'b set)\<close>
  assumes mult_A: \<open>f multipliable_on A\<close>
  assumes BA: \<open>B \<subseteq> A\<close>
  assumes nz: \<open>\<And>x. x \<in> A - B \<Longrightarrow> f x \<noteq> 0\<close>
  shows \<open>f multipliable_on B\<close>
proof (cases "\<exists>x\<in>B. f x = 0")
  case True
  then obtain x where "x \<in> B" "f x = 0" by auto
  then show ?thesis
    unfolding multipliable_on_def using zero_imp_has_setprod_0[of x B f] by auto
next
  case False
  hence nzB: "\<And>x. x \<in> B \<Longrightarrow> f x \<noteq> 0" by auto
  have nzA: "f x \<noteq> 0" if "x \<in> A" for x
    using nz nzB that BA by (cases "x \<in> B") auto
  from mult_A obtain S where limS: \<open>(prod f \<longlongrightarrow> S) (finite_subsets_at_top A)\<close>
    using multipliable_on_def has_setprod_def by blast
  \<comment> \<open>The product net on A is Cauchy (since it converges)\<close>
  have cauchy_A: \<open>cauchy_filter (filtermap (prod f) (finite_subsets_at_top A))\<close>
    using limS by (auto intro!: nhds_imp_cauchy_filter simp: filterlim_def)
  \<comment> \<open>Fix a finite witness F0 from convergence on A (using \<epsilon> = 1, say)\<close>
  obtain F0 where F0_fin: \<open>finite F0\<close> and F0_sub: \<open>F0 \<subseteq> A\<close>
    and F0_P: \<open>\<And>X Y. finite X \<Longrightarrow> F0 \<subseteq> X \<Longrightarrow> X \<subseteq> A \<Longrightarrow> 
                       finite Y \<Longrightarrow> F0 \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> 
                       dist (prod f X) (prod f Y) < 1\<close>
  proof -
    from cauchy_A obtain P where
      ev_P: \<open>eventually P (finite_subsets_at_top A)\<close> and
      P_close: \<open>\<And>X Y. P X \<Longrightarrow> P Y \<Longrightarrow> dist (prod f X) (prod f Y) < 1\<close>
      unfolding cauchy_filter_metric_filtermap
      by (metis zero_less_one)
    from ev_P obtain F0 where \<open>finite F0\<close> \<open>F0 \<subseteq> A\<close>
      \<open>\<And>Z. finite Z \<Longrightarrow> F0 \<subseteq> Z \<Longrightarrow> Z \<subseteq> A \<Longrightarrow> P Z\<close>
      unfolding eventually_finite_subsets_at_top by auto
    then show ?thesis
      using that P_close by force
  qed
  \<comment> \<open>Fix G = F0 - B (the finite part of A outside B from the initial witness)\<close>
  define G where \<open>G = F0 - B\<close>
  have G_fin: \<open>finite G\<close> using F0_fin unfolding G_def by auto
  have G_sub: \<open>G \<subseteq> A - B\<close> using F0_sub unfolding G_def by auto
  have G_disj: \<open>X \<inter> G = {}\<close> if \<open>X \<subseteq> B\<close> for X using that unfolding G_def by auto
  have nz_on_G: \<open>\<And>x. x \<in> G \<Longrightarrow> f x \<noteq> 0\<close> using nz G_sub by auto
  have prod_G_nz: \<open>prod f G \<noteq> 0\<close> using prod_zero_iff[OF G_fin] nz_on_G by auto
  have norm_G_pos: \<open>norm (prod f G) > 0\<close> using prod_G_nz by simp
  \<comment> \<open>Transfer Cauchyness from A to B\<close>
  have cauchy_B: \<open>cauchy_filter (filtermap (prod f) (finite_subsets_at_top B))\<close>
    unfolding cauchy_filter_metric_filtermap
  proof (intro allI impI)
    fix e :: real assume \<open>e > 0\<close>
    \<comment> \<open>Scale epsilon for use with A's Cauchy property\<close>
    define e' where \<open>e' = e / norm (prod f G)\<close>
    have e'_pos: \<open>e' > 0\<close> unfolding e'_def using \<open>e > 0\<close> norm_G_pos by auto
    \<comment> \<open>From Cauchyness on A, get a witness F1 for the scaled epsilon\<close>
    from cauchy_A e'_pos obtain P where
      ev_P: \<open>eventually P (finite_subsets_at_top A)\<close> and
      P_close: \<open>\<And>X Y. P X \<Longrightarrow> P Y \<Longrightarrow> dist (prod f X) (prod f Y) < e'\<close>
      by (auto simp: cauchy_filter_metric_filtermap)
    from ev_P obtain F1 where F1_fin: \<open>finite F1\<close> and F1_sub: \<open>F1 \<subseteq> A\<close>
      and F1_P: \<open>\<And>Z. finite Z \<Longrightarrow> F1 \<subseteq> Z \<Longrightarrow> Z \<subseteq> A \<Longrightarrow> P Z\<close>
      unfolding eventually_finite_subsets_at_top by auto
    \<comment> \<open>Enlarge F1 to contain F0\<close>
    define F1' where \<open>F1' = F1 \<union> F0\<close>
    have F1'_fin: \<open>finite F1'\<close> using F1_fin F0_fin unfolding F1'_def by auto
    have F1'_sub: \<open>F1' \<subseteq> A\<close> using F1_sub F0_sub unfolding F1'_def by auto
    have F1_sub_F1': \<open>F1 \<subseteq> F1'\<close> unfolding F1'_def by auto
    have F0_sub_F1': \<open>F0 \<subseteq> F1'\<close> unfolding F1'_def by auto
    have F1'_P: \<open>P Z\<close> if \<open>finite Z\<close> \<open>F1' \<subseteq> Z\<close> \<open>Z \<subseteq> A\<close> for Z
      using F1_P[OF that(1) _ that(3)] that(2) F1_sub_F1' by auto
    \<comment> \<open>W is the B-part of F1'\<close>
    define W where \<open>W = F1' \<inter> B\<close>
    have W_fin: \<open>finite W\<close> using F1'_fin unfolding W_def by auto
    have W_sub: \<open>W \<subseteq> B\<close> unfolding W_def by auto
    \<comment> \<open>For X \<subseteq> B with W \<subseteq> X, the set X \<union> G contains F1'\<close>
    have F1'_sub_XG: \<open>F1' \<subseteq> X \<union> G\<close> if \<open>W \<subseteq> X\<close> \<open>X \<subseteq> B\<close> for X
    proof
      fix x assume \<open>x \<in> F1'\<close>
      show \<open>x \<in> X \<union> G\<close>
      proof (cases \<open>x \<in> B\<close>)
        case True
        then have \<open>x \<in> F1' \<inter> B\<close> using \<open>x \<in> F1'\<close> by auto
        then have \<open>x \<in> W\<close> unfolding W_def by auto
        then show ?thesis using that(1) by auto
      next
        case False
        then have \<open>x \<in> F1' - B\<close> using \<open>x \<in> F1'\<close> by auto
        then have \<open>x \<in> A - B\<close> using F1'_sub by auto
        moreover have \<open>x \<in> F0\<close> 
          \<comment> \<open>x \<in> F1' = F1 \<union> F0 and x \<notin> B, but we need x \<in> F0 for x \<in> G = F0 - B\<close>
          \<comment> \<open>Actually, x \<in> F1' - B = (F1 \<union> F0) - B, which contains F0 - B = G\<close>
          \<comment> \<open>but also F1 - B. We need F1' - B \<subseteq> G = F0 - B, i.e., F1 - B \<subseteq> F0 - B.\<close>
          \<comment> \<open>This doesn't hold in general!\<close>
          sorry
        ultimately show ?thesis unfolding G_def by auto
      qed
    qed
    then show "\<And>e. 0 < e \<Longrightarrow>
         \<exists>P. eventually P (finite_subsets_at_top B) \<and>
             (\<forall>x y. P x \<and> P y \<longrightarrow> dist (prod f x) (prod f y) < e)"
      sorry
  qed
  \<comment> \<open>Completeness gives convergence\<close>
  from cauchy_B obtain L where \<open>filtermap (prod f) (finite_subsets_at_top B) \<le> nhds L\<close>
    using cauchy_filter_complete_converges[of \<open>filtermap (prod f) (finite_subsets_at_top B)\<close> UNIV]
      complete by (auto simp: filtermap_bot_iff)
  then show ?thesis
    by (auto simp: multipliable_on_def has_setprod_def filterlim_def)
qed

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
proof -
  from infprod have lim_g: \<open>(prod g \<longlongrightarrow> x) (finite_subsets_at_top S)\<close>
    by (simp add: has_setprod_def)
  \<comment> \<open>Compose f with the limit: since isCont f x and prod g \<rightarrow> x, we get f \<circ> prod g \<rightarrow> f x\<close>
  have \<open>((f \<circ> prod g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
  proof (rule topological_tendstoI)
    fix U assume \<open>open U\<close> \<open>f x \<in> U\<close>
    with cont[unfolded continuous_at_open]
    obtain V where \<open>open V\<close> \<open>x \<in> V\<close> and V_sub: \<open>\<And>y. y \<in> V \<Longrightarrow> f y \<in> U\<close>
      by (metis continuous_at_open isCont_def)
    from lim_g[THEN topological_tendstoD, OF \<open>open V\<close> \<open>x \<in> V\<close>]
    show \<open>\<forall>\<^sub>F F in finite_subsets_at_top S. (f \<circ> prod g) F \<in> U\<close>
      by (eventually_elim) (auto intro: V_sub)
  qed
  moreover have \<open>\<forall>\<^sub>F F in finite_subsets_at_top S. prod (f \<circ> g) F = (f \<circ> prod g) F\<close>
    by (rule eventually_finite_subsets_at_top_weakI) (use f_sum in auto)
  ultimately have \<open>(prod (f \<circ> g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
    using tendsto_cong by blast
  then show ?thesis
    by (simp add: has_setprod_def)
qed

lemma multipliable_on_comm_multiplicative_general:
  fixes f :: \<open>'b :: {banach, field, topological_semigroup_mult} \<Rightarrow> 'c :: {banach, field, topological_semigroup_mult}\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> prod (f \<circ> g) F = f (prod g F)\<close>
    \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes \<open>\<And>x. (g has_setprod x) S \<Longrightarrow> f \<midarrow>x\<rightarrow> f x\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes \<open>g multipliable_on S\<close>
  shows \<open>(f \<circ> g) multipliable_on S\<close>
  by (meson assms multipliable_on_def has_setprod_comm_multiplicative_general has_setprod_def infprod_tendsto)

lemma infprod_comm_additive_general:
  fixes f :: \<open>'b :: {banach, field, topological_semigroup_mult} \<Rightarrow> 'c :: {banach, field, topological_semigroup_mult}\<close>
  assumes f_sum: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> prod (f \<circ> g) F = f (prod g F)\<close>
      \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes \<open>isCont f (infprod g S)\<close>
  assumes \<open>g multipliable_on S\<close>
  shows \<open>infprod (f \<circ> g) S = f (infprod g S)\<close>
  using assms
  by (intro infprodI has_setprod_comm_multiplicative_general has_setprod_infprod) (auto simp: isCont_def)

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
      using assms inj_on_subset by blast
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

(*
  TODO from Manuel: Like the subset one:
  This is broken. It assumed that multiplication is uniformly convergent, which it isn't.

  One probably has to assume strong multipliability or, even better, that all multiplicands are 
  nonzero (which can then be generalised to strong multipliability).

  Then it holds that all multiplicands are "away from 0 and close to 1", i.e. 
  they are all contained in some ball around 1 that does not contain 0. (you showed something
  roughly like this already in has_setprod_factors_tend_to_1).

  Then everything probably works again because multiplication is uniformly continuous on such 
  domains.

  It might also be a good idea to just switch to real_normed_field in order to avoid messing around
  with uniformity (which I always find very confusing). You lose some generality that way, but
  it still gives us the result for real and complex, which are the important ones.
*)
lemma has_setprod_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::real_normed_field\<close>
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
          sorry
          (* TODO from Manuel: broken because I deleted an inconsistent assumption *)
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
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_field\<close>
  assumes multipliableAB: "(\<lambda>(x,y). f x y) multipliable_on (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x) multipliable_on (B x)\<close>
  shows \<open>(\<lambda>x. infprod (f x) (B x)) multipliable_on A\<close>
proof -
  from multipliableAB obtain a where a: \<open>((\<lambda>(x,y). f x y) has_setprod a) (Sigma A B)\<close>
    using has_setprod_infprod by blast
  from multipliableB have b: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x has_setprod infprod (f x) (B x)) (B x)\<close>
    by (auto intro!: has_setprod_infprod)
  show ?thesis
    using a b
    by (smt (verit) has_setprod_Sigma[where f=\<open>\<lambda>(x,y). f x y\<close>] has_setprod_cong old.prod.case multipliable_on_def) 
qed

lemma infprod_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::real_normed_field\<close>
  assumes multipliableAB: "f multipliable_on (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (\<lambda>y. f (x, y)) multipliable_on (B x)\<close>
  shows "infprod f (Sigma A B) = infprod (\<lambda>x. infprod (\<lambda>y. f (x, y)) (B x)) A"
proof -
  from multipliableAB have a: \<open>(f has_setprod infprod f (Sigma A B)) (Sigma A B)\<close>
    using has_setprod_infprod by blast
  from multipliableB have b: \<open>\<And>x. x\<in>A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod infprod (\<lambda>y. f (x, y)) (B x)) (B x)\<close>
    by (auto intro!: has_setprod_infprod)
  show ?thesis
    using a b by (auto intro: infprodI[symmetric] has_setprod_Sigma simp: multipliable_on_def)
qed

lemma infprod_Sigma':
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_field\<close>
  assumes multipliableAB: "(\<lambda>(x,y). f x y) multipliable_on (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x) multipliable_on (B x)\<close>
  shows \<open>infprod (\<lambda>x. infprod (f x) (B x)) A = infprod (\<lambda>(x,y). f x y) (Sigma A B)\<close>
  using infprod_Sigma[of \<open>\<lambda>(x,y). f x y\<close> A B]
  using assms by auto

(*
  TODO from Manuel: all of these might require strongly_multipliable_on.
*)
lemma
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{banach,real_normed_field}\<close>
  assumes [simp]: "(\<lambda>(x,y). f x y) multipliable_on (Sigma A B)"
  assumes nz: \<open>\<And>x y. (x, y) \<in> Sigma A B \<Longrightarrow> f x y \<noteq> 0\<close>
  shows infprod_Sigma'_banach: \<open>infprod (\<lambda>x. infprod (f x) (B x)) A = infprod (\<lambda>(x,y). f x y) (Sigma A B)\<close> (is ?thesis1)
    and multipliable_on_Sigma_banach: \<open>(\<lambda>x. infprod (f x) (B x)) multipliable_on A\<close> (is ?thesis2)
  sorry

lemma infprod_Sigma_banach:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{banach,real_normed_field}\<close>
  assumes [simp]: "f multipliable_on (Sigma A B)"
  assumes \<open>\<And>x y. (x, y) \<in> Sigma A B \<Longrightarrow> f (x, y) \<noteq> 0\<close>
  shows \<open>infprod (\<lambda>x. infprod (\<lambda>y. f (x,y)) (B x)) A = infprod f (Sigma A B)\<close>
  using assms
  by (metis (no_types, lifting) case_prod_eta infprod_Sigma'_banach infprod_cong)

lemma infprod_swap:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_field"
  assumes \<open>(\<lambda>(x, y). f x y) multipliable_on (A \<times> B)\<close>
  assumes \<open>\<And>a. a\<in>A \<Longrightarrow> (f a) multipliable_on B\<close>
  assumes \<open>\<And>b. b\<in>B \<Longrightarrow> (\<lambda>a. f a b) multipliable_on A\<close>
  shows \<open>infprod (\<lambda>x. infprod (\<lambda>y. f x y) B) A = infprod (\<lambda>y. infprod (\<lambda>x. f x y) A) B\<close>
proof -
  have "(\<lambda>(x, y). f y x) \<circ> prod.swap multipliable_on A \<times> B"
    by (simp add: assms(1) multipliable_on_cong)
  then have fyx: \<open>(\<lambda>(x, y). f y x) multipliable_on (B \<times> A)\<close>
    by (metis has_setprod_reindex infprod_reindex inj_swap product_swap multipliable_iff_has_setprod_infprod)
  have \<open>infprod (\<lambda>x. infprod (\<lambda>y. f x y) B) A = infprod (\<lambda>(x,y). f x y) (A \<times> B)\<close>
    using infprod_Sigma' assms by blast
  also have \<open>\<dots> = infprod (\<lambda>(x,y). f y x) (B \<times> A)\<close>
    by (simp add: product_swap [symmetric, of B] infprod_reindex o_def)
  also have \<open>\<dots> = infprod (\<lambda>y. infprod (\<lambda>x. f x y) A) B\<close>
    using assms(3) fyx infprod_Sigma by force
  finally show ?thesis .
qed

lemma infprod_swap_banach:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::{banach,real_normed_field}"
  assumes \<open>(\<lambda>(x, y). f x y) multipliable_on (A \<times> B)\<close>
  assumes nz: \<open>\<And>x y. x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> f x y \<noteq> 0\<close>
  assumes times_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x*y)\<close>
  shows "infprod (\<lambda>x. infprod (\<lambda>y. f x y) B) A = infprod (\<lambda>y. infprod (\<lambda>x. f x y) A) B"
proof -
  have \<section>: \<open>(\<lambda>(x, y). f y x) multipliable_on (B \<times> A)\<close>
    by (metis (mono_tags, lifting) assms case_swap inj_swap o_apply product_swap multipliable_on_cong multipliable_on_reindex)
  have nz1: \<open>\<And>x y. (x, y) \<in> Sigma A (\<lambda>_. B) \<Longrightarrow> f x y \<noteq> 0\<close>
    using nz by auto
  have nz2: \<open>\<And>x y. (x, y) \<in> Sigma B (\<lambda>_. A) \<Longrightarrow> f y x \<noteq> 0\<close>
    using nz by auto
  have \<open>infprod (\<lambda>x. infprod (\<lambda>y. f x y) B) A = infprod (\<lambda>(x,y). f x y) (A \<times> B)\<close>
    using assms nz1 infprod_Sigma'_banach by blast
  also have \<open>\<dots> = infprod (\<lambda>(x,y). f y x) (B \<times> A)\<close>
    apply (subst product_swap[symmetric])
    apply (subst infprod_reindex)
    using assms by (auto simp: o_def)
  also have \<open>\<dots> = infprod (\<lambda>y. infprod (\<lambda>x. f x y) A) B\<close>
    by (metis (mono_tags, lifting) \<section> nz2 times_cont infprod_Sigma'_banach infprod_cong)
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
  assumes "(f has_setprod (inverse a)) A" and "a \<noteq> 0"
  shows   \<open>((\<lambda>x. inverse (f x)) has_setprod a) A\<close>
proof (rule has_setprodI)
  from assms(1) have lim: \<open>(prod f \<longlongrightarrow> inverse a) (finite_subsets_at_top A)\<close>
    by (rule has_setprodD)
  from assms(2) have \<open>inverse a \<noteq> 0\<close> by simp
  from tendsto_inverse[OF lim this] have \<open>((\<lambda>X. inverse (prod f X)) \<longlongrightarrow> inverse (inverse a)) (finite_subsets_at_top A)\<close> .
  also have \<open>inverse (inverse a) = a\<close> using assms(2) by simp
  finally show \<open>((\<lambda>X. prod (\<lambda>x. inverse (f x)) X) \<longlongrightarrow> a) (finite_subsets_at_top A)\<close>
    by (simp add: prod_inversef[symmetric] o_def)
qed

lemma has_setprod_inverse_iff:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "a \<noteq> 0"
  shows \<open>((\<lambda>x. inverse (f x)) has_setprod a) A \<longleftrightarrow> (f has_setprod (inverse a)) A\<close>
proof
  assume h: \<open>((\<lambda>x. inverse (f x)) has_setprod a) A\<close>
  have \<open>a = inverse (inverse a)\<close> using assms by simp
  with h have \<open>((\<lambda>x. inverse (f x)) has_setprod (inverse (inverse a))) A\<close> by simp
  from has_setprod_inverse[OF this] assms show \<open>(f has_setprod (inverse a)) A\<close>
    by (simp add: inverse_inverse_eq)
next
  assume \<open>(f has_setprod (inverse a)) A\<close>
  from has_setprod_inverse[OF this] assms show \<open>((\<lambda>x. inverse (f x)) has_setprod a) A\<close> by simp
qed

lemma multipliable_on_inverse:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A" and "infprod f A \<noteq> 0"
  shows   "(\<lambda>x. inverse (f x)) multipliable_on A"
proof -
  from assms(1) have \<open>(f has_setprod (infprod f A)) A\<close>
    by (rule has_setprod_infprod)
  moreover have \<open>infprod f A = inverse (inverse (infprod f A))\<close>
    using assms(2) by simp
  ultimately have \<open>(f has_setprod (inverse (inverse (infprod f A)))) A\<close>
    by simp
  from has_setprod_inverse[OF this] assms(2) 
  have \<open>((\<lambda>x. inverse (f x)) has_setprod (inverse (infprod f A))) A\<close>
    by simp
  thus ?thesis
    unfolding multipliable_on_def by blast
qed


lemma infprod_inverse:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes \<open>f multipliable_on A\<close> and \<open>infprod f A \<noteq> 0\<close>
  shows \<open>infprod (\<lambda>x. inverse (f x)) A = inverse (infprod f A)\<close>
proof -
  have \<open>(f has_setprod (infprod f A)) A\<close>
    using assms(1) by (rule has_setprod_infprod)
  moreover have \<open>infprod f A = inverse (inverse (infprod f A))\<close>
    using assms(2) by simp
  ultimately have \<open>(f has_setprod (inverse (inverse (infprod f A)))) A\<close>
    by simp
  from has_setprod_inverse[OF this] assms(2)
  have \<open>((\<lambda>x. inverse (f x)) has_setprod (inverse (infprod f A))) A\<close>
    by simp
  thus ?thesis by (rule infprodI)
qed

lemma multipliable_on_inverse_iff:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  shows \<open>(f multipliable_on A \<and> infprod f A \<noteq> 0) \<longleftrightarrow>
         ((\<lambda>x. inverse (f x)) multipliable_on A \<and> infprod (\<lambda>x. inverse (f x)) A \<noteq> 0)\<close>
proof (intro iffI conjI)
  assume asm: \<open>f multipliable_on A \<and> infprod f A \<noteq> 0\<close>
  then show \<open>(\<lambda>x. inverse (f x)) multipliable_on A\<close>
    by (intro multipliable_on_inverse) auto
  from asm show \<open>infprod (\<lambda>x. inverse (f x)) A \<noteq> 0\<close>
    by (simp add: infprod_inverse)
next
  assume asm: \<open>(\<lambda>x. inverse (f x)) multipliable_on A \<and> infprod (\<lambda>x. inverse (f x)) A \<noteq> 0\<close>
  then have mult_inv: \<open>(\<lambda>x. inverse (f x)) multipliable_on A\<close> and
            nz_inv: \<open>infprod (\<lambda>x. inverse (f x)) A \<noteq> 0\<close> by auto
  from multipliable_on_inverse[OF mult_inv nz_inv]
  have inv_mult: \<open>(\<lambda>x. inverse (inverse (f x))) multipliable_on A\<close> .
  then show \<open>f multipliable_on A\<close>
    using multipliable_on_cong[of A \<open>\<lambda>x. inverse (inverse (f x))\<close> f] by auto
  from infprod_inverse[OF mult_inv nz_inv]
  have \<open>infprod (\<lambda>x. inverse (inverse (f x))) A = inverse (infprod (\<lambda>x. inverse (f x)) A)\<close> .
  moreover have \<open>infprod (\<lambda>x. inverse (inverse (f x))) A = infprod f A\<close>
    by (intro infprod_cong) auto
  ultimately show \<open>infprod f A \<noteq> 0\<close>
    using nz_inv by simp
qed


lemma has_setprod_power_int:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "(f has_setprod P) A" and "P \<noteq> 0"
  shows   "((\<lambda>x. f x powi n) has_setprod (P powi n)) A"
proof (cases \<open>n \<ge> 0\<close>)
  case True
  then show ?thesis
    using assms(1) by (auto simp: power_int_def intro!: has_setprod_power)
next
  case False
  then have \<open>P ^ nat (- n) \<noteq> 0\<close> using assms(2) by auto
  with False show ?thesis
    using assms(1) by (auto simp: power_int_def power_inverse intro!: has_setprod_power has_setprod_inverse)
qed

lemma multipliable_on_power_int:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A" and "infprod f A \<noteq> 0"
  shows   "(\<lambda>x. f x powi n) multipliable_on A"
proof (cases \<open>n \<ge> 0\<close>)
  case True
  then show ?thesis
    using assms(1) by (auto simp: power_int_def intro!: multipliable_on_power)
next
  case False
  have \<open>(\<lambda>x. f x ^ nat (-n)) multipliable_on A\<close>
    using assms(1) by (rule multipliable_on_power)
  moreover have \<open>infprod (\<lambda>x. f x ^ nat (-n)) A \<noteq> 0\<close>
    using assms by (simp add: infprod_power)
  ultimately have \<open>(\<lambda>x. inverse (f x ^ nat (-n))) multipliable_on A\<close>
    by (rule multipliable_on_inverse)
  with False show ?thesis
    by (auto simp: power_int_def power_inverse)
qed

lemma infprod_power_int:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f multipliable_on A" and "infprod f A \<noteq> 0"
  shows \<open>infprod (\<lambda>x. f x powi n) A = infprod f A powi n\<close>
  using infprod_inverse
infprod_power
  using assms has_setprod_power_int infprodI multipliable_iff_has_setprod_infprod by blast

lemma has_sum_imp_has_setprod_exp:
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

lemma multipliable_on_exp:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach,real_normed_field}\<close>
  assumes "f summable_on A"
  shows   "(\<lambda>x. exp (f x)) multipliable_on A"
proof -
  from assms obtain S where S: "(f has_sum S) A"
    by (auto simp: summable_on_def)
  show ?thesis
    using has_sum_imp_has_setprod_exp[OF S]  has_setprod_imp_multipliable by blast
qed

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
  fixes f :: "'a \<Rightarrow> 'b :: {ring_1_no_zero_divisors, discrete_topology, topological_comm_monoid_mult, semidom}"
  shows "f multipliable_on A \<longleftrightarrow> (\<exists>x\<in>A. f x = 0) \<or> finite {x\<in>A. f x \<noteq> 1}"
proof
  assume \<open>(\<exists>x\<in>A. f x = 0) \<or> finite {x\<in>A. f x \<noteq> 1}\<close>
  then show \<open>f multipliable_on A\<close>
  proof
    assume \<open>\<exists>x\<in>A. f x = 0\<close>
    then obtain x where \<open>x \<in> A\<close> \<open>f x = 0\<close> by auto
    with zero_imp_has_setprod_0
    show \<open>f multipliable_on A\<close> unfolding multipliable_on_def by metis
  next
    assume *: \<open>finite {x\<in>A. f x \<noteq> 1}\<close>
    hence \<open>f multipliable_on {x\<in>A. f x \<noteq> 1}\<close>
      by (rule multipliable_on_finite)
    then show \<open>f multipliable_on A\<close>
      by (smt (verit) DiffE mem_Collect_eq multipliable_on_cong_neutral)
  qed
next
  assume \<open>f multipliable_on A\<close>
  then obtain S where S: \<open>(f has_setprod S) A\<close>
    by (auto simp: multipliable_on_def)
  hence \<open>\<forall>\<^sub>F x in finite_subsets_at_top A. prod f x = S\<close>
    unfolding has_setprod_def tendsto_discrete .
  then obtain X where X: \<open>finite X\<close> \<open>X \<subseteq> A\<close> \<open>\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod f Y = S\<close>
    unfolding eventually_finite_subsets_at_top by metis
  have prodX: \<open>prod f X = S\<close> using X by auto
  show \<open>(\<exists>x\<in>A. f x = 0) \<or> finite {x\<in>A. f x \<noteq> 1}\<close>
  proof (cases \<open>S = 0\<close>)
    case True
    then have \<open>prod f X = 0\<close> using prodX by simp
    then obtain x where \<open>x \<in> X\<close> \<open>f x = 0\<close>
      using X(1) by (metis prod_zero_iff)
    with X(2) show ?thesis by auto
  next
    case False
    have \<open>{x\<in>A. f x \<noteq> 1} \<subseteq> X\<close>
    proof
      fix x assume x: \<open>x \<in> {x\<in>A. f x \<noteq> 1}\<close>
      show \<open>x \<in> X\<close>
      proof (rule ccontr)
        assume [simp]: \<open>x \<notin> X\<close>
        have \<open>prod f (insert x X) = S\<close>
          using X x by (intro X) auto
        then have \<open>f x * prod f X = S\<close>
          using X(1) by simp
        then have \<open>f x * S = S\<close> using prodX by simp
        with False have \<open>f x = 1\<close>
          by (metis mult_cancel_right1)
        with x show False by auto
      qed
    qed
    thus ?thesis using X(1) finite_subset by blast
  qed
qed

lemma has_setprod_imp_has_prod:
  fixes f :: \<open>nat \<Rightarrow> 'a::real_normed_field\<close>
  assumes \<open>(f has_setprod S) (UNIV :: nat set)\<close> and \<open>convergent_prod f\<close>
  shows \<open>f has_prod S\<close>
proof -
  from assms(1) have \<open>(prod f \<longlongrightarrow> S) (finite_subsets_at_top UNIV)\<close>
    by (simp add: has_setprod_def)
  then have lim_S: \<open>(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> S\<close>
  proof (rule filterlim_compose)
    show \<open>filterlim (\<lambda>n. {..n}) (finite_subsets_at_top UNIV) sequentially\<close>
      using filterlim_atMost_at_top by auto
  qed
  from assms(2) have lim_P: \<open>(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> prodinf f\<close>
    using convergent_prod_LIMSEQ by blast
  from lim_S lim_P have \<open>S = prodinf f\<close>
    by (rule LIMSEQ_unique)
  with assms(2) show \<open>f has_prod S\<close>
    using convergent_prod_has_prod by blast
qed

lemma multipliable_on_imp_convergent_prod:
  fixes f :: \<open>nat \<Rightarrow> 'a::real_normed_field\<close>
  assumes \<open>f multipliable_on (UNIV :: nat set)\<close> and \<open>infprod f UNIV \<noteq> 0\<close>
  shows \<open>convergent_prod f\<close>
proof -
  define S where \<open>S = infprod f UNIV\<close>
  from assms(1) have \<open>(f has_setprod S) UNIV\<close>
    unfolding S_def by (rule has_setprod_infprod)
  then have lim: \<open>(prod f \<longlongrightarrow> S) (finite_subsets_at_top UNIV)\<close>
    by (simp add: has_setprod_def)
  then have seq_lim: \<open>(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> S\<close>
  proof (rule filterlim_compose)
    show \<open>filterlim (\<lambda>n. {..n}) (finite_subsets_at_top UNIV) sequentially\<close>
      using filterlim_atMost_at_top by auto
  qed
  \<comment> \<open>Since S \<noteq> 0, eventually partial products are nonzero\<close>
  from seq_lim assms(2)[folded S_def] have \<open>\<forall>\<^sub>F n in sequentially. prod f {..n} \<noteq> 0\<close>
    by (intro tendsto_imp_eventually_ne) auto
  then obtain N where N: \<open>\<And>n. n \<ge> N \<Longrightarrow> prod f {..n} \<noteq> 0\<close>
    by (auto simp: eventually_at_top_linorder)
  have fnz: \<open>f n \<noteq> 0\<close> if \<open>n > N\<close> for n
  proof -
    from N[of n] N[of \<open>n - 1\<close>] that
    have \<open>prod f {..n} \<noteq> 0\<close> \<open>prod f {..n-1} \<noteq> 0\<close> by auto
    moreover have \<open>prod f {..n} = f n * prod f {..n-1}\<close> using that
      by (metis Suc_pred' gr_implies_not_zero mult.commute not_gr_zero prod.atMost_Suc)
    ultimately show \<open>f n \<noteq> 0\<close> by auto
  qed
  \<comment> \<open>The shifted sequence converges to a nonzero limit\<close>
  have \<open>convergent_prod (\<lambda>i. f (i + Suc N))\<close>
  proof -
    have lim: \<open>(\<lambda>n. \<Prod>i\<le>n. f (i + Suc N)) \<longlonglongrightarrow> S / prod f {..N}\<close>
    proof -
      have \<open>(\<lambda>n. prod f {..n + Suc N}) \<longlonglongrightarrow> S\<close>
        using seq_lim LIMSEQ_ignore_initial_segment
        by blast
      moreover have \<open>prod f {..n + Suc N} = prod f {..N} * prod (\<lambda>i. f (i + Suc N)) {..n}\<close> for n
      proof -
        have \<open>{..n + Suc N} = {..N} \<union> {Suc N..n + Suc N}\<close> by auto
        also have \<open>prod f \<dots> = prod f {..N} * prod f {Suc N..n + Suc N}\<close>
          by (subst prod.union_disjoint) auto
        also have \<open>prod f {Suc N..n + Suc N} = prod (\<lambda>i. f (i + Suc N)) {..n}\<close>
          by (metis (no_types) add_0 atMost_atLeast0 prod.shift_bounds_cl_nat_ivl)
        finally show ?thesis .
      qed
      ultimately have \<open>(\<lambda>n. prod f {..N} * prod (\<lambda>i. f (i + Suc N)) {..n}) \<longlonglongrightarrow> S\<close>
        by (simp add: tendsto_cong)
      then have \<open>(\<lambda>n. prod f {..N} * prod (\<lambda>i. f (i + Suc N)) {..n} / prod f {..N}) \<longlonglongrightarrow> S / prod f {..N}\<close>
        using N[of N, simplified]
        by (intro tendsto_divide tendsto_const) auto
      then show ?thesis
        using N[of N, simplified] by (simp add: field_simps)
    qed
    moreover have \<open>S / prod f {..N} \<noteq> 0\<close>
      using assms(2)[folded S_def] N[of N, simplified] by auto
    ultimately have \<open>raw_has_prod (\<lambda>i. f (i + Suc N)) 0 (S / prod f {..N})\<close>
      by (simp add: raw_has_prod_def)
    then show ?thesis
      unfolding convergent_prod_def by blast
  qed
  then show \<open>convergent_prod f\<close>
    by (rule convergent_prod_offset)
qed

lemma has_prod_imp_sums_ln_real: 
  fixes f :: "'a \<Rightarrow> real"
  assumes "(f has_setprod p) A" "p \<noteq> 0"
  shows "((\<lambda>x. ln (f x)) has_sum (ln p)) A"
proof -
  have nz: "f x \<noteq> 0" if "x \<in> A" for x
    using assms that by (metis infprodI zero_imp_has_setprod_0)
  have "((\<lambda>X. ln (prod f X)) \<longlongrightarrow> ln p) (finite_subsets_at_top A)"
  proof (rule tendsto_ln)
    show "(prod f \<longlongrightarrow> p) (finite_subsets_at_top A)"
      using assms(1) unfolding has_setprod_def by blast
  qed (use assms in auto)
  also have "?this \<longleftrightarrow> (sum (\<lambda>x. ln (f x)) \<longlongrightarrow> ln p) (finite_subsets_at_top A)"
  proof (intro filterlim_cong)
    have "\<forall>\<^sub>F X in finite_subsets_at_top A. X \<subseteq> A \<and> finite X"
      by (rule eventually_finite_subsets_at_top_weakI) auto
    thus "\<forall>\<^sub>F x in finite_subsets_at_top A. ln (prod f x) = (\<Sum>x\<in>x. ln (f x))"
      by eventually_elim (subst ln_prod, use nz in auto)
  qed auto
  finally show ?thesis
    unfolding has_sum_def .
qed


subsection \<open>Strong multipliability\<close>

lemma strongly_multipliable_imp_multipliable:
  assumes "f strongly_multipliable_on A"
  shows   "f multipliable_on A"
proof -
  from assms obtain P where P: "finite {x\<in>A. f x = 0}" "(f has_setprod P) {x\<in>A. f x \<noteq> 0}"
    by (auto simp: strongly_multipliable_on_def)
  have "(f has_setprod (P * prod f {x\<in>A. f x = 0})) ({x\<in>A. f x \<noteq> 0} \<union> {x\<in>A. f x = 0})"
    by (intro has_setprod_Un_disjoint P has_setprod_finite) auto
  also have "{x\<in>A. f x \<noteq> 0} \<union> {x\<in>A. f x = 0} = A"
    by auto
  finally show ?thesis
    by (rule has_setprod_imp_multipliable)
qed

text \<open>
  For a non-zero family, strong multipliability is equivalent to the product being non-zero.
\<close>
lemma strongly_multipliable_on_nonzero_iff:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows   "f strongly_multipliable_on A \<longleftrightarrow> (\<exists>P. (f has_setprod P) A \<and> P \<noteq> 0)"
proof
  assume *: "(\<exists>P. (f has_setprod P) A \<and> P \<noteq> 0)"
  from assms have [simp]: "{x\<in>A. f x = 0} = {}" "{x\<in>A. f x \<noteq> 0} = A"
    by auto
  from * obtain P where P: "(f has_setprod P) A" "P \<noteq> 0"
    by blast
  thus "f strongly_multipliable_on A"
    by (auto simp: strongly_multipliable_on_def assms)
next
  assume "f strongly_multipliable_on A"
  then obtain P where "(f has_setprod P) {x\<in>A. f x \<noteq> 0} \<and> P \<noteq> 0"
    by (auto simp: strongly_multipliable_on_def)
  also have "{x\<in>A. f x \<noteq> 0} = A"
    using assms by auto
  finally show "\<exists>P. (f has_setprod P) A \<and> P \<noteq> 0"
    by blast
qed

lemma strongly_multipliable_on_Diff_finite:
  fixes f :: "_ \<Rightarrow> 'a :: real_normed_field"
  assumes "f strongly_multipliable_on A" "finite B"
  shows   "f strongly_multipliable_on (A - B)"
proof -
  from assms(1) obtain P where P: "finite {x\<in>A. f x = 0}" "(f has_setprod P) {x\<in>A. f x \<noteq> 0}" "P \<noteq> 0"
    by (auto simp: strongly_multipliable_on_def)
  define Q where "Q = prod f {x\<in>B\<inter>A. f x \<noteq> 0}"
  have Q: "(f has_setprod Q) {x\<in>B\<inter>A. f x \<noteq> 0}"
    unfolding Q_def by (intro has_setprod_finite) (use assms(2) in auto)
  have [simp]: "Q \<noteq> 0"
    using assms(2) by (auto simp: Q_def)

  have "(f has_setprod (P / Q)) ({x\<in>A. f x \<noteq> 0} - {x\<in>B\<inter>A. f x \<noteq> 0})"
    by (intro has_setprod_Diff P Q) auto
  also have "{x\<in>A. f x \<noteq> 0} - {x\<in>B\<inter>A. f x \<noteq> 0} = {x\<in>A-B. f x \<noteq> 0}"
    by blast
  finally have "(f has_setprod P / Q) {x\<in>A-B. f x \<noteq> 0}" .
  moreover have "finite {x\<in>A-B. f x = 0}"
    by (rule finite_subset[OF _ P(1)]) auto
  moreover have "P / Q \<noteq> 0"
    using P(3) by auto
  ultimately show ?thesis
    unfolding strongly_multipliable_on_def by blast
qed

lemma abs_multipliable_on_imp_strongly_multipliable_on:
  assumes "f abs_multipliable_on A"
  shows   "f strongly_multipliable_on A"
  sorry


subsection \<open>Absolute convergence\<close>

(*
  TODO from Manuel: why does this use the explicit limit rather than has_setprod?
  Also, this seems a bit too concrete for my taste. One should be able to prove something like
  the version below in a more general setting (but it will probably require a bit of juggling
  with uniformity).
*)
lemma has_setprod_factors_tend_to_1:
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_div_algebra,comm_monoid_mult}"
  assumes lim: "(prod f \<longlongrightarrow> L) (finite_subsets_at_top M)" and nz: "L \<noteq> 0"
  shows "\<forall>\<epsilon>>0. \<exists>F. finite F \<and> F \<subseteq> M \<and> (\<forall>x\<in>M - F. dist (f x) 1 < \<epsilon>)"
proof (intro allI impI)
  fix \<epsilon> :: real assume "\<epsilon> > 0"
  define \<delta> where "\<delta> = min (\<epsilon> * norm L / 4) (norm L / 4)"
  have "\<delta> > 0" unfolding \<delta>_def using \<open>\<epsilon> > 0\<close> nz
    by (simp add: zero_less_norm_iff)
  have \<delta>_le1: "\<delta> \<le> \<epsilon> * norm L / 4" and \<delta>_le2: "\<delta> \<le> norm L / 4"
    unfolding \<delta>_def by auto
  from tendstoD[OF lim \<open>\<delta> > 0\<close>]
  obtain F0 where F0_fin: "finite F0" and F0_sub: "F0 \<subseteq> M"
    and F0_close: "\<And>Y. finite Y \<Longrightarrow> F0 \<subseteq> Y \<Longrightarrow> Y \<subseteq> M \<Longrightarrow> dist (prod f Y) L < \<delta>"
    unfolding eventually_finite_subsets_at_top
    by metis
  \<comment> \<open>Show that prod f F0 is bounded away from 0\<close>
  have dist_F0: "dist (prod f F0) L < \<delta>" using F0_close F0_fin F0_sub by auto
  have "norm (prod f F0 - L) < norm L / 4"
    using dist_F0 \<delta>_le2 by (simp add: dist_norm)
  moreover have "norm L - norm (prod f F0 - L) \<le> norm (prod f F0)"
    by (metis dist_commute dist_diff(1) dist_norm norm_triangle_ineq2)
  ultimately have norm_F0: "norm (prod f F0) > norm L / 2"
    using norm_ge_zero[of L] by linarith
  hence prod_F0_nz: "prod f F0 \<noteq> 0" by auto
  \<comment> \<open>For any x outside F0, f x is close to 1\<close>
  show "\<exists>F. finite F \<and> F \<subseteq> M \<and> (\<forall>x\<in>M - F. dist (f x) 1 < \<epsilon>)"
  proof (intro exI conjI ballI)
    show "finite F0" by fact
    show "F0 \<subseteq> M" by fact
    fix x assume "x \<in> M - F0"
    hence "x \<in> M" "x \<notin> F0" by auto
    have "dist (prod f (F0 \<union> {x})) L < \<delta>"
      using F0_close[of "F0 \<union> {x}"] F0_fin \<open>x \<in> M\<close> F0_sub by auto
    hence "dist (prod f (F0 \<union> {x})) (prod f F0) < 2 * \<delta>"
      using dist_F0 by (smt (verit) dist_triangle dist_commute)
    moreover have "prod f (F0 \<union> {x}) = f x * prod f F0"
      using prod.insert[OF F0_fin \<open>x \<notin> F0\<close>] by (simp add: insert_absorb)
    ultimately have "dist (f x * prod f F0) (1 * prod f F0) < 2 * \<delta>"
      by simp
    hence "norm (prod f F0) * dist (f x) 1 < 2 * \<delta>"
      by (metis dist_norm left_diff_distrib norm_mult mult.commute)
    hence "dist (f x) 1 < 2 * \<delta> / norm (prod f F0)"
      using norm_F0
      by (simp add: mult.commute mult_imp_less_div_pos prod_F0_nz)
    also have "\<dots> < 2 * \<delta> / (norm L / 2)"
      by (metis \<open>0 < \<delta>\<close> frac_less2 half_gt_zero mult_pos_pos norm_F0 nz order.refl zero_less_norm_iff
          zero_less_numeral)
    also have "\<dots> \<le> 2 * (\<epsilon> * norm L / 4) / (norm L / 2)"
      using \<delta>_le1 nz by (intro divide_right_mono mult_left_mono) (auto simp: zero_less_norm_iff)
    also have "\<dots> = \<epsilon>" using nz
      by (simp add: zero_less_norm_iff)
    finally show "dist (f x) 1 < \<epsilon>" .
  qed
qed

(* Specialised to real_normed_div_algebra following Manuel's advice. *)
lemma has_setprod_factors_tend_to_1':
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_div_algebra, comm_monoid_mult}"
  assumes lim: "(prod f \<longlongrightarrow> L) (finite_subsets_at_top M)" and nz: "L \<noteq> 0"
  assumes X: "open X" "1 \<in> X"
  shows "\<exists>F. finite F \<and> F \<subseteq> M \<and> (\<forall>x\<in>M - F. f x \<in> X)"
proof -
  from X obtain \<epsilon> where "\<epsilon> > 0" and ball_sub: "ball 1 \<epsilon> \<subseteq> X"
    using openE by blast
  from has_setprod_factors_tend_to_1[OF lim nz, rule_format, OF \<open>\<epsilon> > 0\<close>]
  obtain F where "finite F" "F \<subseteq> M" "\<And>x. x \<in> M - F \<Longrightarrow> dist (f x) 1 < \<epsilon>"
    by blast
  then show ?thesis
    using ball_sub by (intro exI[of _ F]) (auto simp: ball_def dist_commute)
qed

text \<open>
  For a strongly multipliable family, all but finitely many values are close to 1.
\<close>
lemma strongly_multipliable_on_imp_nhds_1:
  fixes f :: "_ \<Rightarrow> 'a :: {real_normed_div_algebra,semidom}"
  assumes "f strongly_multipliable_on A" "open X" "1 \<in> X"
  shows "\<exists>B. B \<subseteq> A \<and> finite B \<and> (\<forall>x\<in>A-B. f x \<in> X)"
proof -
  from assms(1) obtain P 
    where P: "finite {x\<in>A. f x = 0}" "(f has_setprod P) {x\<in>A. f x \<noteq> 0}" "P \<noteq> 0"
    by (auto simp: strongly_multipliable_on_def)
  have "\<exists>F. finite F \<and> F \<subseteq> {x \<in> A. f x \<noteq> 0} \<and> (\<forall>x\<in>{x \<in> A. f x \<noteq> 0} - F. f x \<in> X)"
    by (rule has_setprod_factors_tend_to_1'[where L = P])
       (use assms P in \<open>auto simp: has_setprod_def\<close>)
  then obtain F where F: "finite F" "F \<subseteq> {x\<in>A. f x \<noteq> 0}" "\<forall>x\<in>{x \<in> A. f x \<noteq> 0} - F. f x \<in> X"
    by blast
  define B where "B = F \<union> {x\<in>A. f x = 0}"
  have "B \<subseteq> A" "finite B" "\<forall>x\<in>A-B. f x \<in> X"
    unfolding B_def using F P by auto
  thus ?thesis
    by blast
qed

text \<open>
  The equivalent for summable familes: In a summable family, all but finitely many elements are
  close to 0.
\<close>
(* Specialised to real_normed_field following Manuel's advice. *)
lemma summable_on_imp_nhds_0:
  fixes f :: "'a \<Rightarrow> 'b :: real_normed_field"
  assumes lim: "f summable_on M"
  assumes X: "open X" "0 \<in> X"
  shows "\<exists>F. finite F \<and> F \<subseteq> M \<and> (\<forall>x\<in>M - F. f x \<in> X)"
proof -
  from lim obtain S where S: "(f has_sum S) M"
    unfolding summable_on_def by blast
  hence tend: "((\<lambda>U. sum f U) \<longlongrightarrow> S) (finite_subsets_at_top M)"
    by (auto simp: has_sum_def)
  \<comment> \<open>Find open W around S such that a - b \<in> X whenever a, b \<in> W\<close>
  have "continuous_on UNIV (\<lambda>(a::'b, b). a - b)"
    by (auto intro!: continuous_intros simp: case_prod_unfold)
  hence cont: "isCont (\<lambda>(a::'b, b). a - b) (S, S)"
    by (simp add: continuous_on_eq_continuous_at)
  from cont[unfolded isCont_def] have "((\<lambda>(a,b). a - b) \<longlongrightarrow> (0::'b)) (nhds (S, S))"
    by (simp add: tendsto_nhds_iff)
  from this[unfolded tendsto_def, rule_format, OF X(1) X(2)]
  have "eventually (\<lambda>(a,b). a - b \<in> X) (nhds (S, S))"
    by (simp add: case_prod_unfold)
  hence "\<forall>\<^sub>F (a, b) in nhds S \<times>\<^sub>F nhds S. a - b \<in> X"
    by (simp add: nhds_prod[symmetric])
  then obtain Q where Q_ev: "eventually Q (nhds S)" and Q_sub: "\<And>a b. Q a \<Longrightarrow> Q b \<Longrightarrow> a - b \<in> X"
    unfolding eventually_prod_same by auto
  then obtain W where W: "open W" "S \<in> W" "W \<subseteq> Collect Q"
    unfolding eventually_nhds by auto
  have W_sub: "a - b \<in> X" if "a \<in> W" "b \<in> W" for a b
    using Q_sub that W(3) by auto
  \<comment> \<open>Get F such that all partial sums beyond F are in W\<close>
  from tend have "eventually (\<lambda>U. sum f U \<in> W) (finite_subsets_at_top M)"
    using topological_tendstoD W by blast
  then obtain F where F: "finite F" "F \<subseteq> M" 
    "\<And>U. finite U \<Longrightarrow> F \<subseteq> U \<Longrightarrow> U \<subseteq> M \<Longrightarrow> sum f U \<in> W"
    unfolding eventually_finite_subsets_at_top by metis
  show ?thesis
  proof (intro exI conjI ballI)
    show "finite F" "F \<subseteq> M" by fact+
    fix x assume "x \<in> M - F"
    hence xM: "x \<in> M" and xF: "x \<notin> F" by auto
    have "sum f (insert x F) \<in> W"
      by (intro F) (use F xM in auto)
    moreover have "sum f F \<in> W"
      by (intro F) (use F in auto)
    ultimately have "sum f (insert x F) - sum f F \<in> X"
      by (rule W_sub)
    also have "sum f (insert x F) - sum f F = f x"
      using F(1) xF by simp
    finally show "f x \<in> X" .
  qed
qed
lemma has_setprod_imp_has_prod_nonzero:
  assumes \<open>(f has_setprod S) (UNIV :: nat set)\<close> and \<open>S \<noteq> 0\<close>
  shows   \<open>f has_prod S\<close>
proof -
  from assms(1) have \<open>(prod f \<longlongrightarrow> S) (finite_subsets_at_top UNIV)\<close>
    by (simp add: has_setprod_def)
  then have \<open>(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> S\<close>
  proof (rule filterlim_compose)
    show \<open>filterlim (\<lambda>n. {..n}) (finite_subsets_at_top UNIV) sequentially\<close>
      using filterlim_atMost_at_top by auto
  qed
  with \<open>S \<noteq> 0\<close> have \<open>raw_has_prod f 0 S\<close>
    by (simp add: raw_has_prod_def)
  then show \<open>f has_prod S\<close>
    by (simp add: has_prod_def)
qed

text \<open>
  TODO from Manuel: Again, the precondition "1 \<le> f x" is very strong.
  It would probably make more sense to assume strong multipliability, in which case one can
  probably weaken this to a "0 \<le> f x".
\<close>
lemma finite_sum_le_infprod:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f multipliable_on A" "finite F" "F \<subseteq> A" and ge1: "\<And>x. x \<in> A \<Longrightarrow> 1 \<le> f x"
  shows "prod f F \<le> infprod f A"
proof -
  have nonneg: "0 \<le> f x" if "x \<in> A" for x
    using assms(4)[OF that] by linarith
  have tendsto: "(prod f \<longlongrightarrow> infprod f A) (finite_subsets_at_top A)"
    using infprod_tendsto[OF assms(1)] .
  have "Limsup (finite_subsets_at_top A) (prod f) = infprod f A"
    using finite_subsets_at_top_neq_bot tendsto tendsto_iff_Liminf_eq_Limsup by blast
  moreover have "prod f F \<le> Limsup (finite_subsets_at_top A) (prod f)"
  proof (rule le_Limsup[OF finite_subsets_at_top_neq_bot])
    show "\<forall>\<^sub>F X in finite_subsets_at_top A. ereal (prod f F) \<le> ereal (prod f X)"
      unfolding eventually_finite_subsets_at_top
    proof (intro exI conjI allI impI)
      show "finite F" by fact
      show "F \<subseteq> A" by fact
      fix Y assume "finite Y \<and> F \<subseteq> Y \<and> Y \<subseteq> A"
      then have "finite Y" "F \<subseteq> Y" "Y \<subseteq> A" by auto
      show "ereal (prod f F) \<le> ereal (prod f Y)"
        by (metis Diff_subset \<open>F \<subseteq> Y\<close> \<open>Y \<subseteq> A\<close> \<open>finite Y\<close> ge1 ereal_less_eq(3) in_mono nonneg prod_mono2)
    qed
  qed
  ultimately show ?thesis by simp
qed


lemma abs_multipliable_iff_bdd_above:
  shows \<open>f abs_multipliable_on A \<longleftrightarrow> bdd_above (prod (\<lambda>x. 1 + norm (f x - 1)) ` {F. F\<subseteq>A \<and> finite F})\<close>
proof (rule iffI)
  assume asm: \<open>f abs_multipliable_on A\<close>
  then have mult: \<open>(\<lambda>x. 1 + norm (f x - 1)) multipliable_on A\<close>
    by (simp add: abs_multipliable_on_def)
  show \<open>bdd_above (prod (\<lambda>x. 1 + norm (f x - 1)) ` {F. F \<subseteq> A \<and> finite F})\<close>
  proof (rule bdd_aboveI2)
    fix F assume F: "F \<in> {F. F \<subseteq> A \<and> finite F}"
    then have "finite F" "F \<subseteq> A" by auto
    show "(\<Prod>x\<in>F. 1 + norm (f x - 1)) \<le> (\<Prod>\<^sub>\<infinity>x\<in>A. 1 + norm (f x - 1))"
      by (rule finite_sum_le_infprod[OF mult \<open>finite F\<close> \<open>F \<subseteq> A\<close>]) auto
  qed
next
  assume bdd: \<open>bdd_above (prod (\<lambda>x. 1 + norm (f x - 1)) ` {F. F\<subseteq>A \<and> finite F})\<close>
  show \<open>f abs_multipliable_on A\<close>
    unfolding abs_multipliable_on_def
  proof -
    define g where \<open>g x = 1 + norm (f x - 1)\<close> for x
    have g_ge1: \<open>g x \<ge> 1\<close> for x unfolding g_def by auto
    from bdd obtain C where C: \<open>prod g F \<le> C\<close> if \<open>F \<subseteq> A\<close> \<open>finite F\<close> for F
      unfolding bdd_above_def g_def by auto
    have g_ge0: \<open>g x \<ge> 0\<close> for x using g_ge1[of x] by linarith
    have mono: \<open>prod g F \<le> prod g G\<close> if \<open>F \<subseteq> G\<close> \<open>G \<subseteq> A\<close> \<open>finite G\<close> for F G
      using that g_ge1 g_ge0 by (intro prod_mono2) auto
    have \<open>(prod g \<longlongrightarrow> (SUP F\<in>{F. F \<subseteq> A \<and> finite F}. prod g F)) (finite_subsets_at_top A)\<close>
    proof (rule order_tendstoI)
      fix a :: real assume \<open>a < (SUP F\<in>{F. F \<subseteq> A \<and> finite F}. prod g F)\<close>
      then obtain F where F: \<open>F \<subseteq> A\<close> \<open>finite F\<close> \<open>a < prod g F\<close>
        using less_cSUP_iff[of \<open>{F. F \<subseteq> A \<and> finite F}\<close> \<open>prod g\<close> a]
          bdd[unfolded g_def[abs_def]]
        unfolding g_def by auto
      show \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. a < prod g X\<close>
        unfolding eventually_finite_subsets_at_top
      proof (intro exI[of _ F] conjI allI impI)
        show \<open>finite F\<close> by fact
        show \<open>F \<subseteq> A\<close> by fact
        fix Y assume \<open>finite Y \<and> F \<subseteq> Y \<and> Y \<subseteq> A\<close>
        then show \<open>a < prod g Y\<close>
          using F(3) mono[of F Y] by auto
      qed
    next
      fix a :: real assume \<open>(SUP F\<in>{F. F \<subseteq> A \<and> finite F}. prod g F) < a\<close>
      show \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. prod g X < a\<close>
        unfolding eventually_finite_subsets_at_top
      proof (intro exI[of _ "{}"] conjI allI impI)
        show \<open>finite {}\<close> by simp
        show \<open>{} \<subseteq> A\<close> by simp
        fix Y assume \<open>finite Y \<and> {} \<subseteq> Y \<and> Y \<subseteq> A\<close>
        then have \<open>prod g Y \<le> (SUP F\<in>{F. F \<subseteq> A \<and> finite F}. prod g F)\<close>
          using bdd
          by (intro cSUP_upper bdd[unfolded g_def[abs_def]]) (auto simp: g_def)
        also have \<open>\<dots> < a\<close> by fact
        finally show \<open>prod g Y < a\<close> .
      qed
    qed
    then have \<open>g multipliable_on A\<close>
      unfolding multipliable_on_def has_setprod_def by blast
    then show \<open>(\<lambda>x. 1 + norm (f x - 1)) multipliable_on A\<close>
      unfolding g_def .
  qed
qed

lemma multipliable_on_comparison_test:
  fixes f g :: "'b \<Rightarrow> real"
  assumes "f multipliable_on A" and "\<And>x. x \<in> A \<Longrightarrow> g x \<le> f x" and "\<And>x. x \<in> A \<Longrightarrow> 1 \<le> g x"
  shows   "g multipliable_on A"
proof -
  from assms(1) obtain S where S: "(prod f \<longlongrightarrow> S) (finite_subsets_at_top A)"
    unfolding multipliable_on_def has_setprod_def by blast
  have g_ge1: "1 \<le> g x" if "x \<in> A" for x
    using assms(3)[OF that] .
  have g_nonneg: "0 \<le> g x" if "x \<in> A" for x
    using g_ge1[OF that] by (meson dual_order.trans zero_le_one)
  have g_le_f_prod: "prod g X \<le> prod f X" if "X \<subseteq> A" "finite X" for X
  proof (rule prod_mono)
    fix i assume "i \<in> X"
    with that have "i \<in> A" by auto
    thus "0 \<le> g i \<and> g i \<le> f i"
      using g_nonneg assms(2) by auto
  qed
  have g_mono: "prod g X \<le> prod g Y" if "X \<subseteq> Y" "Y \<subseteq> A" "finite Y" for X Y
  proof (rule prod_mono2[OF \<open>finite Y\<close> \<open>X \<subseteq> Y\<close>])
    fix b assume "b \<in> Y - X"
    with that have "b \<in> A" by auto
    thus "1 \<le> g b" using g_ge1 by auto
  next
    fix a assume "a \<in> X"
    with that have "a \<in> A" by auto
    thus "0 \<le> g a" using g_nonneg by auto
  qed
  have f_bound: "\<exists>C. \<forall>\<^sub>F X in finite_subsets_at_top A. prod f X \<le> C"
  proof (cases "\<exists>C. C > S")
    case True
    then obtain C where C: "C > S" by blast
    have "\<forall>\<^sub>F X in finite_subsets_at_top A. prod f X < C"
      using S C by (rule order_tendstoD)
    thus ?thesis
      by (meson eventually_mono nless_le)
  next
    case False thus ?thesis
      by (meson not_eventuallyD not_le_imp_less)
  qed
  then obtain C where C: "\<forall>\<^sub>F X in finite_subsets_at_top A. prod f X \<le> C"
    by blast
  from C obtain X0 where X0: "finite X0" "X0 \<subseteq> A"
    and X0_bound: "\<And>X. finite X \<Longrightarrow> X0 \<subseteq> X \<Longrightarrow> X \<subseteq> A \<Longrightarrow> prod f X \<le> C"
    unfolding eventually_finite_subsets_at_top by auto
  have g_bdd: "prod g X \<le> C" if "finite X" "X \<subseteq> A" for X
  proof -
    have "prod g X \<le> prod g (X \<union> X0)"
      using that X0 by (intro g_mono) auto
    also have "\<dots> \<le> prod f (X \<union> X0)"
      using that X0 by (intro g_le_f_prod) auto
    also have "\<dots> \<le> C"
      using that X0 X0_bound[of "X \<union> X0"] by auto
    finally show ?thesis .
  qed
  hence bdd: "bdd_above (prod g ` {X. X \<subseteq> A \<and> finite X})"
    by (auto simp: bdd_above_def)
  show ?thesis unfolding multipliable_on_def has_setprod_def
  proof (rule exI, rule increasing_tendsto)
    show "\<forall>\<^sub>F X in finite_subsets_at_top A. prod g X \<le> Sup (prod g ` {X. X \<subseteq> A \<and> finite X})"
      by (intro eventually_finite_subsets_at_top_weakI cSUP_upper[OF _ bdd]) auto
  next
    fix y assume "y < Sup (prod g ` {X. X \<subseteq> A \<and> finite X})"
    then obtain X where X: "X \<subseteq> A" "finite X" "y < prod g X"
      by (subst (asm) less_cSUP_iff[OF _ bdd]) auto
    from X have "eventually (\<lambda>X'. X \<subseteq> X' \<and> X' \<subseteq> A \<and> finite X') (finite_subsets_at_top A)"
      by (auto simp: eventually_finite_subsets_at_top)
    thus "eventually (\<lambda>X'. y < prod g X') (finite_subsets_at_top A)"
    proof eventually_elim
      case (elim X')
      note \<open>y < prod g X\<close>
      also have "prod g X \<le> prod g X'"
        using elim by (intro g_mono) auto
      finally show ?case .
    qed
  qed
qed

lemma abs_multipliable_product:
  fixes x :: "'a \<Rightarrow> 'b::{real_normed_div_algebra,banach,second_countable_topology}"
  assumes x2_sum: "x abs_multipliable_on A"
    and y2_sum: "y abs_multipliable_on A"
  shows "(\<lambda>i. x i * y i) abs_multipliable_on A"
proof -
  define xn yn where "xn i = norm (x i - 1)" and "yn i = norm (y i - 1)" for i
  have xn_nn: "xn i \<ge> 0" for i unfolding xn_def by simp
  have yn_nn: "yn i \<ge> 0" for i unfolding yn_def by simp

  \<comment> \<open>Key inequality: 1 + norm(xy - 1) \<le> (1 + norm(x-1)) * (1 + norm(y-1))\<close>
  have prod_ineq: "1 + norm (x i * y i - 1) \<le> (1 + xn i) * (1 + yn i)" for i
  proof -
    have "x i * y i - 1 = (x i - 1) * (y i - 1) + (x i - 1) + (y i - 1)"
      by (simp add: algebra_simps)
    then have "norm (x i * y i - 1) \<le> norm ((x i - 1) * (y i - 1)) + norm (x i - 1) + norm (y i - 1)"
      by (metis dual_order.refl norm_triangle_mono)
    also have "\<dots> = xn i * yn i + xn i + yn i"
      by (simp add: norm_mult xn_def yn_def)
    finally have "1 + norm (x i * y i - 1) \<le> 1 + xn i * yn i + xn i + yn i"
      by linarith
    also have "\<dots> = (1 + xn i) * (1 + yn i)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed

  \<comment> \<open>From the assumptions, get that (1 + xn) and (1 + yn) are multipliable\<close>
  from x2_sum have xn_mult: "(\<lambda>i. 1 + xn i) multipliable_on A"
    unfolding abs_multipliable_on_def xn_def by simp
  from y2_sum have yn_mult: "(\<lambda>i. 1 + yn i) multipliable_on A"
    unfolding abs_multipliable_on_def yn_def by simp

  \<comment> \<open>Their pointwise product is multipliable\<close>
  have prod_mult: "(\<lambda>i. (1 + xn i) * (1 + yn i)) multipliable_on A"
    by (rule multipliable_on_mult[OF xn_mult yn_mult])

  \<comment> \<open>By comparison, (1 + norm(xy - 1)) is multipliable\<close>
  show "(\<lambda>i. x i * y i) abs_multipliable_on A"
    unfolding abs_multipliable_on_def
  proof (rule multipliable_on_comparison_test[OF prod_mult])
    fix i assume "i \<in> A"
    show "1 + norm (x i * y i - 1) \<le> (1 + xn i) * (1 + yn i)"
      by (rule prod_ineq)
  next
    fix i assume "i \<in> A"
    show "(1::real) \<le> 1 + norm (x i * y i - 1)" by simp
  qed
qed

text \<open>The types @{typ ennreal}, @{typ ereal}, and @{typ enat} cannot be used with the
  infinite-product framework (@{const multipliable_on}, @{const has_setprod}, @{const infprod})
  because it requires @{class semidom}, which demands additive cancellation.
  These types fail cancellation: e.g.\ @{term \<open>(\<infinity>::ennreal) + 1 = \<infinity> + 2\<close>} but @{term \<open>(1::ennreal) \<noteq> 2\<close>}.
  Supporting them would require weakening the type class constraints on the framework definitions.\<close>



(* The correct statement for products requires a nonzero limit (i.e. strongly_multipliable_on),
   since factors must tend to 1 by has_setprod_factors_tend_to_1. *)
lemma multipliable_countable:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {real_normed_div_algebra, semidom}\<close>
  assumes \<open>f strongly_multipliable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 1}\<close>
proof -
  have "\<exists>F. finite F \<and> F \<subseteq> A \<and> (\<forall>x\<in>A - F. f x \<in> ball 1 (1 / real (Suc n)))" for n
    using strongly_multipliable_on_imp_nhds_1[OF assms, of "ball 1 (1 / real (Suc n))"] by auto
  then obtain F where F_fin: "\<And>n. finite (F n)" and F_sub: "\<And>n. F n \<subseteq> A"
    and F_ball: "\<And>n x. x \<in> A - F n \<Longrightarrow> f x \<in> ball 1 (1 / real (Suc n))"
    by metis
  have "{x\<in>A. f x \<noteq> 1} \<subseteq> (\<Union>n. F n)"
  proof (rule subsetI)
    fix x assume "x \<in> {x\<in>A. f x \<noteq> 1}"
    hence "x \<in> A" "f x \<noteq> 1" by auto
    hence "dist (f x) 1 > 0" by auto
    then obtain n where "1 / real (Suc n) < dist (f x) 1"
      using reals_Archimedean[of "dist (f x) 1"]
      by (metis inverse_eq_divide)
    hence "f x \<notin> ball 1 (1 / real (Suc n))"
      by (simp add: dist_commute)
    hence "x \<notin> A - F n"
      using F_ball[of x n] by blast
    hence "x \<in> F n"
      using \<open>x \<in> A\<close> by auto
    thus "x \<in> (\<Union>n. F n)" by auto
  qed
  moreover have "countable (\<Union>n. F n)"
    using F_fin by (intro countable_UN) (auto intro: countable_finite)
  ultimately show ?thesis
    by (rule countable_subset)
qed

lemma multipliable_countable_complex:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>f strongly_multipliable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 1}\<close>
  using assms by (rule multipliable_countable)


lemma prod_norm_le:
  fixes  f::"'b \<Rightarrow> 'a::real_normed_field"
  assumes "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> g x"
  shows "norm (prod f S) \<le> prod g S"
  by (metis norm_ge_zero prod_mono prod_norm assms)

lemma norm_infprod_le:
  fixes  f::"'b \<Rightarrow> 'a::real_normed_field"
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
    by (simp add: assms(3) eventually_finite_subsets_at_top_weakI in_mono prod_norm_le)
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


lemma multipliable_on_imp_bounded_partial_sums:
  fixes f :: "_ \<Rightarrow> 'a :: {topological_semigroup_mult, linorder_topology, semidom, t2_space}"
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



context
  assumes "SORT_CONSTRAINT('a :: {topological_semigroup_mult, order_topology,
             conditionally_complete_linorder, linordered_idom, t2_space})"
begin

text \<open>
  Any family of non-negative numbers with bounded partial sums is multipliable, and the sum
  is simply the supremum of the partial sums.
\<close>
lemma nonneg_bounded_partial_prods_imp_has_setprod_SUP:
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> (1::'a)"
      and bound:  "eventually (\<lambda>X. prod f X \<le> C) (finite_subsets_at_top A)"
  shows   "(f has_setprod (SUP X\<in>{X. X \<subseteq> A \<and> finite X}. prod f X)) A"
proof -
  from bound obtain X0
    where X0: "X0 \<subseteq> A" "finite X0" "\<And>X. X0 \<subseteq> X \<Longrightarrow> X \<subseteq> A \<Longrightarrow> finite X \<Longrightarrow> prod f X \<le> C"
    by (force simp: eventually_finite_subsets_at_top)
  have bound': "prod f X \<le> C" if "X \<subseteq> A" "finite X" for X
  proof -
    have "prod f X \<le> prod f (X \<union> X0)"
      using that X0 assms(1) \<open>finite X0\<close>
      by (smt (verit, best) DiffE dual_order.trans finite_Un nle_le not_one_le_zero prod_mono2 subset_eq sup.bounded_iff)
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
        by (smt (verit) Diff_iff dual_order.trans elim nonneg prod_mono2 subset_iff zero_le_one)
      finally show ?case .
    qed
  qed
qed

lemma nonneg_bounded_partial_sums_imp_multipliable_on:
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> (1::'a)"
      and bound:  "eventually (\<lambda>X. prod f X \<le> C) (finite_subsets_at_top A)"
  shows   "f multipliable_on A"
  using nonneg_bounded_partial_prods_imp_has_setprod_SUP[OF assms] by (auto simp: multipliable_on_def)

end

lemma infprod_nonneg_is_SUPREMUM_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes multipliable: "f multipliable_on A"
    and fge1: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 1"
  shows "infprod f A = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (prod f F))"
proof -
  have fnn: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0" using fge1 by (auto intro: order_trans[OF zero_le_one])
  have lim: "(f has_setprod (infprod f A)) A"
    using multipliable by (rule has_setprod_infprod)
  have bound: "eventually (\<lambda>X. prod f X \<le> infprod f A + 1) (finite_subsets_at_top A)"
  proof -
    from lim[unfolded has_setprod_def]
    have "\<forall>\<^sub>F X in finite_subsets_at_top A. dist (prod f X) (infprod f A) < 1"
      unfolding tendsto_iff by auto
    then show ?thesis
      by eventually_elim (auto simp: dist_real_def abs_le_iff)
  qed
  have sup: "(f has_setprod (SUP X\<in>{X. X \<subseteq> A \<and> finite X}. prod f X)) A"
    by (rule nonneg_bounded_partial_prods_imp_has_setprod_SUP[OF fge1 bound])
  from has_setprod_unique[OF lim] sup
  have "infprod f A = (SUP X\<in>{X. X \<subseteq> A \<and> finite X}. prod f X)" by auto
  also have "{X. X \<subseteq> A \<and> finite X} = {F. finite F \<and> F \<subseteq> A}" by auto
  finally show ?thesis .
qed

lemma has_setprod_nonneg_SUPREMUM_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f multipliable_on A" and "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 1"
  shows "(f has_setprod (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (prod f F))) A"
  by (metis (mono_tags, lifting) assms has_setprod_infprod infprod_nonneg_is_SUPREMUM_real)

lemma infprod_nonneg_is_SUPREMUM_ereal:
  fixes f :: "'a \<Rightarrow> real"
  assumes multipliable: "f multipliable_on A"
    and fge1: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 1"
  shows "ereal (infprod f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (prod f F)))"
proof -
  have real_eq: "infprod f A = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. prod f F)"
    using assms by (rule infprod_nonneg_is_SUPREMUM_real)
  have nonempty: "{F. finite F \<and> F \<subseteq> A} \<noteq> {}"
    by (auto intro: exI[where x="{}"])
  have bdd: "bdd_above (prod f ` {F. finite F \<and> F \<subseteq> A})"
  proof -
    obtain C where C: "eventually (\<lambda>X. prod f X \<le> C) (finite_subsets_at_top A)"
      using multipliable_on_imp_bounded_partial_sums[OF multipliable] by blast
    then obtain X0 where X0: "finite X0" "X0 \<subseteq> A" 
      and bound: "\<And>Y. finite Y \<Longrightarrow> X0 \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod f Y \<le> C"
      unfolding eventually_finite_subsets_at_top by metis
    have "\<And>Y. finite Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod f Y \<le> C"
    proof -
      fix Y assume Y: "finite Y" "Y \<subseteq> A"
      have "prod f Y \<le> prod f (Y \<union> X0)"
        by (rule prod_mono2) (use Y X0 fge1 order_trans[OF zero_le_one] in auto)
      also have "... \<le> C"
        by (rule bound) (use Y X0 in auto)
      finally show "prod f Y \<le> C" .
    qed
    thus ?thesis by (auto intro!: bdd_aboveI[where M=C])
  qed
  have abs_not_inf: "\<bar>SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (prod f F)\<bar> \<noteq> \<infinity>"
  proof -
    have upper: "(SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (prod f F)) \<le> ereal (infprod f A)"
      by (intro cSUP_least) (auto simp: real_eq intro: cSUP_upper bdd)
    have lower: "(SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (prod f F)) \<ge> ereal 1"
      by (intro cSUP_upper2[where x="{}"]) 
         (auto simp: bdd_above_mono[OF _ image_mono] intro!: monoI
               intro: bdd_above_image_mono[OF _ bdd])
    from upper lower show ?thesis by auto
  qed
  show ?thesis
    unfolding real_eq using abs_not_inf by (rule ereal_SUP)
qed

lemma infprod_nonneg_is_SUPREMUM_ennreal:
  fixes f :: "'a \<Rightarrow> real"
  assumes multipliable: "f multipliable_on A"
    and fge1: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 1"
  shows "ennreal (infprod f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (prod f F)))"
  using infprod_nonneg_is_SUPREMUM_ereal[OF assms]
proof -
  have real_eq: "infprod f A = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. prod f F)"
    using assms by (rule infprod_nonneg_is_SUPREMUM_real)
  have prod_nonneg: "prod f F \<ge> 0" if "finite F" "F \<subseteq> A" for F
    using fge1 that by (intro prod_nonneg) (auto intro: order_trans[OF zero_le_one])
  have infprod_nonneg: "infprod f A \<ge> 0"
    using finite_sum_le_infprod[OF multipliable finite.emptyI empty_subsetI fge1] by simp
  have nonempty: "{F. finite F \<and> F \<subseteq> A} \<noteq> {}"
    by auto
  have bdd: "bdd_above (prod f ` {F. finite F \<and> F \<subseteq> A})"
  proof -
    obtain C where "\<And>Y. finite Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod f Y \<le> C"
      using multipliable_on_imp_bounded_partial_sums[OF multipliable]
      using fge1 finite_sum_le_infprod multipliable by blast
    thus ?thesis by (auto intro!: bdd_aboveI)
  qed
  show ?thesis
  proof -
    have "ennreal (Sup (prod f ` {F. finite F \<and> F \<subseteq> A})) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (prod f F))"
    proof (rule antisym)
      show "(SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (prod f F)) \<le> ennreal (Sup (prod f ` {F. finite F \<and> F \<subseteq> A}))"
      proof (rule cSUP_least[OF nonempty])
        fix F assume F: "F \<in> {F. finite F \<and> F \<subseteq> A}"
        have "prod f F \<le> Sup (prod f ` {F. finite F \<and> F \<subseteq> A})"
          using F bdd by (intro cSUP_upper) auto
        thus "ennreal (prod f F) \<le> ennreal (Sup (prod f ` {F. finite F \<and> F \<subseteq> A}))"
          by (rule ennreal_leI)
      qed
    next
      show "ennreal (Sup (prod f ` {F. finite F \<and> F \<subseteq> A})) \<le> (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (prod f F))"
      proof -
        have "Sup (prod f ` {F. finite F \<and> F \<subseteq> A}) \<in> prod f ` {F. finite F \<and> F \<subseteq> A} \<or>
              (\<forall>x \<in> prod f ` {F. finite F \<and> F \<subseteq> A}. x \<le> Sup (prod f ` {F. finite F \<and> F \<subseteq> A}))"
          using bdd by (meson cSup_upper)
        show ?thesis
        proof (rule ennreal_le_epsilon)
          fix e :: real assume "e > 0"
          have Sup_nn: "Sup (prod f ` {F. finite F \<and> F \<subseteq> A}) \<ge> 0"
            using infprod_nonneg real_eq by argo        
          have "Sup (prod f ` {F. finite F \<and> F \<subseteq> A}) - e < Sup (prod f ` {F. finite F \<and> F \<subseteq> A})"
            using \<open>e > 0\<close> by linarith
          then have "\<exists>x\<in>{F. finite F \<and> F \<subseteq> A}. Sup (prod f ` {F. finite F \<and> F \<subseteq> A}) - e < prod f x"
            by (subst (asm) less_cSUP_iff[OF nonempty bdd])
          then obtain F where F: "F \<in> {F. finite F \<and> F \<subseteq> A}" "Sup (prod f ` {F. finite F \<and> F \<subseteq> A}) - e < prod f F"
            by auto
          have "ennreal (Sup (prod f ` {F. finite F \<and> F \<subseteq> A})) \<le> ennreal (prod f F + e)"
            using F \<open>e > 0\<close> by (intro ennreal_leI) linarith
          also have "\<dots> \<le> ennreal (prod f F) + ennreal e"
            using F(1) \<open>0 < e\<close> local.prod_nonneg by force
          also have "ennreal (prod f F) \<le> (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (prod f F))"
            using F(1)
            by (meson Sup_upper image_iff)
          finally show "ennreal (Sup (prod f ` {F. finite F \<and> F \<subseteq> A})) \<le> (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (prod f F)) + ennreal e"
            using add_mono by blast
        qed
      qed
    qed
    thus ?thesis by (simp add: real_eq)
  qed
qed


lemma abs_multipliable_on_iff_summable_on:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra_1}"
  shows "f abs_multipliable_on A \<longleftrightarrow> (\<lambda>n. norm (f n - 1)) summable_on A"
proof
  define g where \<open>g n = norm (f n - 1)\<close> for n
  have g_nn: \<open>g n \<ge> 0\<close> for n unfolding g_def by simp
  assume \<open>f abs_multipliable_on A\<close>
  then obtain L where lim: \<open>((\<lambda>F. \<Prod>x\<in>F. 1 + g x) \<longlongrightarrow> L) (finite_subsets_at_top A)\<close>
    unfolding abs_multipliable_on_def multipliable_on_def has_setprod_def g_def by blast
  show \<open>(\<lambda>n. norm (f n - 1)) summable_on A\<close>
    unfolding g_def[symmetric]
  proof (rule nonneg_bounded_partial_sums_imp_summable_on)
    show \<open>\<And>x. x \<in> A \<Longrightarrow> 0 \<le> g x\<close> using g_nn by simp
    from lim have \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. dist (prod (\<lambda>x. 1 + g x) X) L < 1\<close>
      unfolding tendsto_iff by auto
    then have \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. prod (\<lambda>x. 1 + g x) X < L + 1\<close>
      by (eventually_elim) (auto simp: dist_real_def)
    then show \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. sum g X \<le> L + 1\<close>
    proof eventually_elim
      case (elim X)
      have \<open>sum g X \<le> prod (\<lambda>x. 1 + g x) X\<close>
        by (rule sum_le_prod) (use g_nn in auto)
      also have \<open>\<dots> < L + 1\<close> by (rule elim)
      finally show ?case by linarith
    qed
  qed
next
  define g where \<open>g n = norm (f n - 1)\<close> for n
  have g_nn: \<open>g n \<ge> 0\<close> for n unfolding g_def by simp
  assume \<open>(\<lambda>n. norm (f n - 1)) summable_on A\<close>
  then obtain L where lim: \<open>(sum g \<longlongrightarrow> L) (finite_subsets_at_top A)\<close>
    unfolding summable_on_def has_sum_def g_def by blast
  show \<open>f abs_multipliable_on A\<close>
    unfolding abs_multipliable_on_def g_def[symmetric]
  proof (rule nonneg_bounded_partial_sums_imp_multipliable_on)
    show \<open>\<And>x. x \<in> A \<Longrightarrow> 1 \<le> (\<lambda>x. 1 + g x) x\<close> using g_nn by auto
    \<comment> \<open>Partial products are bounded by exp(L+1)\<close>
    from lim have \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. dist (sum g X) L < 1\<close>
      unfolding tendsto_iff by auto
    then have sum_bound: \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. sum g X < L + 1\<close>
      by (eventually_elim) (auto simp: dist_real_def)
    show \<open>\<forall>\<^sub>F X in finite_subsets_at_top A. prod (\<lambda>x. 1 + g x) X \<le> exp (L + 1)\<close>
      using sum_bound
    proof eventually_elim
      case (elim X)
      have \<open>prod (\<lambda>x. 1 + g x) X \<le> exp (sum g X)\<close>
        by (rule prod_le_exp_sum) (use g_nn in auto)
      also have \<open>\<dots> \<le> exp (L + 1)\<close>
        using elim by simp
      finally show ?case .
    qed
  qed
qed

lemma abs_multipliable_on_comparison_test:
  fixes f :: \<open>'a \<Rightarrow> 'b::{banach, real_normed_algebra_1}\<close>
    and g :: \<open>'a \<Rightarrow> 'c::{banach, real_normed_algebra_1}\<close>
  assumes \<open>g abs_multipliable_on A\<close>
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> norm (f x - 1) \<le> norm (g x - 1)\<close>
  shows   \<open>f abs_multipliable_on A\<close>
proof -
  \<comment> \<open>Step 1: From g abs_multipliable, get that partial sums of norm(g x - 1) are bounded\<close>
  define gn where \<open>gn x = norm (g x - 1)\<close> for x
  define fn where \<open>fn x = norm (f x - 1)\<close> for x
  have gn_nn: \<open>gn x \<ge> 0\<close> for x unfolding gn_def by simp
  have fn_nn: \<open>fn x \<ge> 0\<close> for x unfolding fn_def by simp
  have fn_le_gn: \<open>fn x \<le> gn x\<close> if \<open>x \<in> A\<close> for x
    unfolding fn_def gn_def using assms(2)[OF that] by simp
  \<comment> \<open>The partial products of (1 + gn) converge\<close>
  from assms(1) have k_mult: \<open>(\<lambda>x. 1 + gn x) multipliable_on A\<close>
    unfolding abs_multipliable_on_def gn_def by simp
  from infprod_tendsto[OF k_mult]
  have k_tendsto: \<open>(prod (\<lambda>x. 1 + gn x) \<longlongrightarrow> infprod (\<lambda>x. 1 + gn x) A) (finite_subsets_at_top A)\<close> .
  \<comment> \<open>So partial products are eventually bounded\<close>
  from tendstoD[OF k_tendsto, of 1]
  have \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. dist (prod (\<lambda>x. 1 + gn x) F) (infprod (\<lambda>x. 1 + gn x) A) < 1\<close>
    by simp
  then have prod_bound: \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. prod (\<lambda>x. 1 + gn x) F < infprod (\<lambda>x. 1 + gn x) A + 1\<close>
    by (eventually_elim) (auto simp: dist_real_def)
  \<comment> \<open>Partial sums of gn are bounded by partial products\<close>
  have sum_bound: \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. sum gn F \<le> infprod (\<lambda>x. 1 + gn x) A + 1\<close>
    using prod_bound
  proof eventually_elim
    case (elim F)
    have \<open>sum gn F \<le> prod (\<lambda>x. 1 + gn x) F\<close>
      by (rule sum_le_prod) (use gn_nn in auto)
    also have \<open>\<dots> < infprod (\<lambda>x. 1 + gn x) A + 1\<close> by (rule elim)
    finally show ?case by linarith
  qed
  \<comment> \<open>Step 2: gn is summable\<close>
  have gn_summable: \<open>gn summable_on A\<close>
    by (rule nonneg_bounded_partial_sums_imp_summable_on) (use gn_nn sum_bound in auto)
  \<comment> \<open>Step 3: fn is summable by comparison\<close>
  have fn_bound: \<open>\<exists>C. \<forall>\<^sub>F F in finite_subsets_at_top A. sum fn F \<le> C\<close>
  proof -
    from summable_on_imp_bounded_partial_sums[OF gn_summable]
    obtain C where C: \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. sum gn F \<le> C\<close> by auto
    have FA: \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. F \<subseteq> A\<close>
      by (auto simp: eventually_finite_subsets_at_top)
    from C FA have \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. sum fn F \<le> C\<close>
    proof eventually_elim
      case (elim F)
      have \<open>sum fn F \<le> sum gn F\<close>
        by (intro sum_mono) (use fn_le_gn elim in auto)
      also have \<open>\<dots> \<le> C\<close> by (rule elim)
      finally show ?case .
    qed
    thus ?thesis by auto
  qed
  have fn_summable: \<open>fn summable_on A\<close>
    using fn_bound fn_nn
    by (auto intro!: nonneg_bounded_partial_sums_imp_summable_on)
  show \<open>f abs_multipliable_on A\<close>
    using fn_summable unfolding fn_def
    by (subst abs_multipliable_on_iff_summable_on)
qed

lemma abs_multipliable_on_exp:
  fixes f :: "'a \<Rightarrow> 'b :: {real_normed_field, banach}"
  assumes "f abs_summable_on A"
  shows   "(\<lambda>x. exp (f x)) abs_multipliable_on A"
  unfolding abs_multipliable_on_iff_summable_on
proof -
  obtain B where B: "finite B" "B \<subseteq> A" "\<forall>x\<in>A-B. f x \<in> ball 0 (1/2)"
    using summable_on_imp_nhds_0[OF abs_summable_summable[OF assms(1)], of "ball 0 (1/2)"] by auto
  have "(\<lambda>x. exp (f x) - 1) abs_summable_on (A-B)"
  proof (rule summable_on_comparison_test)
    show "(\<lambda>x. 3/2 * norm (f x)) summable_on (A - B)"
      by (intro summable_on_cmult_right summable_on_subset[OF assms]) auto
  next
    fix x assume x: "x \<in> A - B"
    have "norm (f x) \<le> 1 / 2"
      by (intro less_imp_le) (use B x in auto)
    thus "norm (exp (f x) - 1) \<le> 3/2 * norm (f x)"
      using norm_exp_bounds(2)[of "f x"] by simp
  qed auto
  hence "(\<lambda>x. exp (f x) - 1) abs_summable_on (A - B \<union> B)"
    by (intro summable_on_Un_disjoint) (use B in auto)
  also have "A - B \<union> B = A"
    using B by blast
  finally show "(\<lambda>x. exp (f x) - 1) abs_summable_on A" .
qed



(*
class topological_field = topological_comm_monoid_mult + field +
  assumes tendsto_inverse_nhds: "a \<noteq> 0 \<Longrightarrow> (inverse \<longlongrightarrow> inverse a) (nhds a)"
*)

lemma multipliable_on_union:
  fixes f :: "_ \<Rightarrow> 'a :: real_normed_field"
  assumes "f multipliable_on A" "f multipliable_on B"
  shows "f multipliable_on (A \<union> B)"
proof (cases "\<exists>x\<in>A \<union> B. f x = 0")
  case True
  then obtain x where "x \<in> A \<union> B" "f x = 0" by auto
  then show ?thesis
    unfolding multipliable_on_def using zero_imp_has_setprod_0
    by metis
next
  case False
  hence nz: "\<And>x. x \<in> A \<union> B \<Longrightarrow> f x \<noteq> 0" by auto
  then have "f multipliable_on (B - A)"
    apply (intro multipliable_on_subset_aux[OF _ assms(2) Diff_subset])
     apply (auto simp: )
    sorry
  then show ?thesis
    using assms(1)
    by (metis Diff_disjoint Un_Diff_cancel multipliable_on_Un_disjoint)
qed

lemma multipliable_on_insert_iff:
  fixes f :: "_ \<Rightarrow> 'a :: {real_normed_field, complete_space}"
  assumes "f x \<noteq> 0"
  shows "f multipliable_on insert x A \<longleftrightarrow> f multipliable_on A"
proof
  assume "f multipliable_on A"
  then show "f multipliable_on insert x A"
    using multipliable_on_union[of f A "{x}"] by simp
next
  assume *: "f multipliable_on insert x A"
  show "f multipliable_on A"
  proof (rule multipliable_on_subset_aux[OF complete_UNIV *])
    show "A \<subseteq> insert x A" by auto
  next
    fix y assume "y \<in> insert x A - A"
    hence "y = x" by auto
    with assms show "f y \<noteq> 0" by simp
  qed
qed

lemma has_setprod_finiteI: "finite A \<Longrightarrow> S = prod f A \<Longrightarrow> (f has_setprod S) A"
  by simp

lemma has_setprod_insert:
  fixes f :: "'a \<Rightarrow> 'b :: {topological_comm_monoid_mult, semidom, t2_space}"
  assumes "x \<notin> A" and "(f has_setprod S) A"
  shows   "(f has_setprod (f x * S)) (insert x A)"
proof -
  have "(f has_setprod (f x * S)) ({x} \<union> A)"
    using assms by (intro has_setprod_Un_disjoint) (auto intro: has_setprod_finiteI)
  thus ?thesis by simp
qed

lemma infprod_insert:
  fixes f :: "_ \<Rightarrow> 'a :: {topological_comm_monoid_mult, semidom, t2_space}"
  assumes "f multipliable_on A" "a \<notin> A"
  shows   "infprod f (insert a A) = f a * infprod f A"
  by (meson assms has_setprod_insert infprodI multipliable_iff_has_setprod_infprod)

(* {real_normed_algebra,comm_ring_1, topological_comm_monoid_mult, semidom, t2_space, t3_space} ?*)
lemma has_setprod_SigmaD:
  fixes f :: "'b \<times> 'c \<Rightarrow> 'a :: real_normed_field"
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
      proof (rule tendsto_prod[where f="\<lambda>i B'. prod (\<lambda>y. f (i, y)) (B' i)" and L=g, simplified])
        fix x assume x: "x \<in> Z"
        hence x': "x \<in> A" using 3 by auto
        have tend_x: "((\<lambda>S. prod (\<lambda>y. f (x, y)) S) \<longlongrightarrow> g x) (finite_subsets_at_top (B x))"
          using sum2[OF x'] unfolding has_setprod_def .
        have filt: "filterlim (\<lambda>p. p x) (finite_subsets_at_top (B x))
               (filtercomap (\<lambda>p. p x) (finite_subsets_at_top (B x)))"
          by (rule filterlim_filtercomap)
        have step1: "((\<lambda>B'. prod (\<lambda>y. f (x, y)) (B' x)) \<longlongrightarrow> g x)
               (filtercomap (\<lambda>p. p x) (finite_subsets_at_top (B x)))"
          by (rule filterlim_compose[OF tend_x filt])
        have step2: "(INF x\<in>Z. filtercomap (\<lambda>p. p x) (finite_subsets_at_top (B x))) \<le>
                       filtercomap (\<lambda>p. p x) (finite_subsets_at_top (B x))"
          using x by (rule INF_lower)
        show "((\<lambda>B'. prod (\<lambda>y. f (x, y)) (B' x)) \<longlongrightarrow> g x)
                         (INF x\<in>Z. filtercomap (\<lambda>p. p x) (finite_subsets_at_top (B x)))"
          using step1 step2 tendsto_mono by blast
      qed
      show "\<forall>\<^sub>F x in H. (\<Prod>xa\<in>Z. \<Prod>y\<in>x xa. f (xa, y)) \<in> X'" 
        sorry
      show "H \<noteq> bot"
        apply (auto simp: H_def) sorry
    qed
  next
    show "finite Y1"
      using Y(2) Y1_def by blast
    show "\<And>x. x \<in> Y1 \<Longrightarrow> x \<in> A"
      using Y1 by blast
    show "\<And>Y. finite Y \<Longrightarrow> Y1 \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod g Y \<in> X"
      sorry
  qed
qed


lemma has_setprod_SigmaI:
  fixes f :: "_ \<Rightarrow> 'a :: real_normed_field"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod g x) (B x)"
  assumes g: "(g has_setprod S) A"
  assumes multipliable: "f multipliable_on Sigma A B"
  shows   "(f has_setprod S) (Sigma A B)"
  by (metis f g has_setprod_SigmaD has_setprod_infprod has_setprod_unique local.multipliable)

lemma multipliable_on_SigmaD1:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> 'a :: {real_normed_field, complete_space}"
  assumes f: "(\<lambda>(x,y). f x y) multipliable_on Sigma A B"
  assumes x: "x \<in> A"
  assumes nz: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> B a \<Longrightarrow> a \<noteq> x \<Longrightarrow> f a b \<noteq> 0"
  shows   "f x multipliable_on B x"
proof (cases "\<exists>b\<in>B x. f x b = 0")
  case True
  then obtain b where "b \<in> B x" "f x b = 0" by auto
  then show ?thesis
    unfolding multipliable_on_def using zero_imp_has_setprod_0
    by metis
next
  case False
  have step1: "(\<lambda>(x,y). f x y) multipliable_on Sigma {x} B"
  proof (rule multipliable_on_subset_aux[OF complete_UNIV f])
    show "Sigma {x} B \<subseteq> Sigma A B"
      using x by auto
  next
    fix p assume "p \<in> Sigma A B - Sigma {x} B"
    then show "(case p of (x, y) \<Rightarrow> f x y) \<noteq> 0"
      using nz by (cases p) auto
  qed
  have step2: "(\<lambda>y. f x y) \<circ> snd multipliable_on Sigma {x} B"
    using step1 multipliable_on_cong[of "Sigma {x} B" "\<lambda>(a,b). f a b" "(\<lambda>y. f x y) \<circ> snd"]
    by auto
  have inj: "inj_on snd (Sigma {x} B)"
    by (auto intro!: inj_onI simp: Sigma_def)
  have step3: "(\<lambda>y. f x y) multipliable_on snd ` Sigma {x} B"
    using step2 multipliable_on_reindex[OF inj, of "\<lambda>y. f x y"] by simp
  have "snd ` Sigma {x} B = B x"
    by (force simp: Sigma_def)
  with step3 show ?thesis by simp
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

(*
lemma has_setprod_cmult_right_iff:
  fixes c :: "'a :: {topological_semigroup_mult, field, t2_space}"
  assumes "c \<noteq> 0"
  shows   "((\<lambda>x. c * f x) has_setprod S) A \<longleftrightarrow> (f has_setprod (S / c)) A"
  \<comment> \<open>WARNING: This statement is FALSE for |A| \<noteq> 1. 
      Counterexample: A = {1,2}, f = (\<lambda>_. 1), c = 2. LHS product = 4, RHS product = 1 \<noteq> 4/2.
      The correct version would need c^(card A) for finite A.\<close>
  oops

lemma has_setprod_cmult_left_iff:
  fixes c :: "'a :: {topological_semigroup_mult, field, t2_space}"
  assumes "c \<noteq> 0"
  shows   "((\<lambda>x. f x * c) has_setprod S) A \<longleftrightarrow> (f has_setprod (S / c)) A"
  oops
*)

lemma finite_nonzero_values_imp_multipliable_on:
  assumes "finite {x\<in>X. f x \<noteq> 0}"
  shows   "f multipliable_on X"
proof (cases "finite X")
  case True
  then show ?thesis by simp
next
  case False
  then have "X - {x\<in>X. f x \<noteq> 0} \<noteq> {}"
    using assms by (metis Collect_mem_eq Diff_eq_empty_iff finite_subset subset_refl)
  then obtain x where "x \<in> X" "f x = 0" by auto
  then have "(f has_setprod 0) X"
    by (rule zero_imp_has_setprod_0)
  then show ?thesis
    unfolding multipliable_on_def by blast
qed

lemma multipliable_on_of_int_iff:
  "(\<lambda>x::'a. of_int (f x) :: 'b :: {real_normed_algebra_1, topological_semigroup_mult, semidom}) multipliable_on A \<longleftrightarrow> f multipliable_on A"
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
    have eq: "of_int (prod f X) = (of_int (prod f Y) :: 'b)"
    proof (rule ccontr)
      assume "of_int (prod f X) \<noteq> (of_int (prod f Y) :: 'b)"
      hence "prod f X \<noteq> prod f Y" by auto
      hence "abs (prod f X - prod f Y) \<ge> 1" 
        by (simp del: of_int_prod of_nat_prod)
      hence "norm (of_int (prod f X - prod f Y) :: 'b) \<ge> 1"
        by (simp add: norm_of_int del: of_int_prod of_nat_prod of_int_diff)
      hence "norm (of_int (prod f X) - (of_int (prod f Y) :: 'b)) \<ge> 1"
        by (simp add: of_int_diff)
      moreover have "(of_int (prod f X) :: 'b) = prod (\<lambda>x. of_int (f x)) X"
        using X(1) by (induction X rule: finite_induct) (auto simp: of_int_mult)
      moreover have "(of_int (prod f Y) :: 'b) = prod (\<lambda>x. of_int (f x)) Y"
        using that(1) by (induction Y rule: finite_induct) (auto simp: of_int_mult)
      ultimately show False
        using \<open>dist (prod (\<lambda>x. of_int (f x)) X) (prod (\<lambda>x. of_int (f x) :: 'b) Y) < 1/2 + 1/2\<close>
        by (simp add: dist_norm)
    qed
    thus ?thesis 
      using eq by (simp add: of_int_eq_iff del: of_int_prod of_nat_prod)
  qed
  have "(prod f \<longlongrightarrow> prod f X) (finite_subsets_at_top A)"
  proof (rule tendsto_eventually)
    show "\<forall>\<^sub>F Y in finite_subsets_at_top A. prod f Y = prod f X"
      unfolding eventually_finite_subsets_at_top
      using X(1,2) \<open>\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod f Y = prod f X\<close>
      by blast
  qed
  thus "f multipliable_on A"
    unfolding multipliable_on_def has_setprod_def by blast
qed

lemma multipliable_on_of_nat_iff:
  "(\<lambda>x::'a. of_nat (f x) :: 'b :: {real_normed_algebra_1, semidom, topological_semigroup_mult}) multipliable_on A \<longleftrightarrow> f multipliable_on A"
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
  proof
    have prod_int: "prod (\<lambda>x. int (f x)) X = int (prod f X)" if "finite X" for X
      using that by (induction X rule: finite_induct) auto
    show "(\<lambda>x. int (f x)) multipliable_on A \<Longrightarrow> f multipliable_on A"
    proof -
      assume "(\<lambda>x. int (f x)) multipliable_on A"
      then obtain S where lim: "(prod (\<lambda>x. int (f x)) \<longlongrightarrow> S) (finite_subsets_at_top A)"
        by (auto simp: multipliable_on_def has_setprod_def)
      have "\<forall>\<^sub>F X in finite_subsets_at_top A. prod (\<lambda>x. int (f x)) X = S"
        using lim by (simp add: tendsto_discrete)
      then obtain X where X: "finite X" "X \<subseteq> A"
        "\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod (\<lambda>x. int (f x)) Y = S"
        unfolding eventually_finite_subsets_at_top by metis
      have "prod f Y = prod f X" if "finite Y" "X \<subseteq> Y" "Y \<subseteq> A" for Y
      proof -
        have "int (prod f X) = prod (\<lambda>x. int (f x)) X"
          using prod_int[OF X(1)] by simp
        also have "\<dots> = S" by (rule X(3)) (use X in auto)
        also have "\<dots> = prod (\<lambda>x. int (f x)) Y" by (rule X(3)[symmetric]) (use that in auto)
        also have "\<dots> = int (prod f Y)"
          using prod_int[OF that(1)] by simp
        finally show ?thesis by presburger
      qed
      hence "(prod f \<longlongrightarrow> prod f X) (finite_subsets_at_top A)"
        by (intro tendsto_eventually)
           (auto simp: eventually_finite_subsets_at_top intro!: exI[of _ X] X(1,2))
      thus "f multipliable_on A"
        unfolding multipliable_on_def has_setprod_def by blast
    qed
    show "f multipliable_on A \<Longrightarrow> (\<lambda>x. int (f x)) multipliable_on A"
      by (rule multipliable_on_homomorphism) auto
  qed
  finally show "f multipliable_on A" .
qed

lemma infprod_of_nat:
  "infprod (\<lambda>x::'a. of_nat (f x) :: 'b :: {real_normed_algebra_1, semidom, topological_semigroup_mult}) A = of_nat (infprod f A)"
  by (metis has_setprod_empty has_setprod_infprod has_setprod_of_nat infprodI infprod_def
      multipliable_on_of_nat_iff)

lemma infprod_of_int:
  "infprod (\<lambda>x::'a. of_int (f x) :: 'b :: {real_normed_algebra_1, semidom, topological_semigroup_mult}) A = of_int (infprod f A)"
  by (metis has_setprod_infprod has_setprod_of_int infprodI infprod_not_exists
      multipliable_on_of_int_iff of_int_1)


lemma multipliable_on_SigmaI:
  fixes f :: "_ \<Rightarrow> 'a :: {linorder_topology, linordered_idom, topological_comm_monoid_mult,
                          conditionally_complete_linorder}"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod g x) (B x)"
  assumes g: "g multipliable_on A"
  assumes f_nonneg: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> f (x, y) \<ge> 1"
  shows   "f multipliable_on Sigma A B"
proof -
  have g_ge1: "g x \<ge> 1" if "x \<in> A" for x
  proof (rule ccontr)
    assume "\<not> g x \<ge> 1"
    then have "g x < 1" by auto
    from f[OF that] have lim: "(prod (\<lambda>y. f (x, y)) \<longlongrightarrow> g x) (finite_subsets_at_top (B x))"
      by (simp add: has_setprod_def)
    from order_tendstoD(2)[OF lim \<open>g x < 1\<close>]
    have "\<forall>\<^sub>F X in finite_subsets_at_top (B x). prod (\<lambda>y. f (x, y)) X < 1"
      by simp
    moreover have "\<forall>\<^sub>F X in finite_subsets_at_top (B x). prod (\<lambda>y. f (x, y)) X \<ge> 1"
      unfolding eventually_finite_subsets_at_top
      by (intro exI[of _ "{}"] conjI allI impI)
         (auto intro!: prod_ge_1 dest: subsetD intro: f_nonneg[OF that])
    ultimately show False
      using eventually_elim2 finite_subsets_at_top_neq_bot eventually_False
      by (metis \<open>\<not> 1 \<le> g x\<close> lim tendsto_lowerbound)
  qed
  have g_nonneg: "g x \<ge> 0" if "x \<in> A" for x
    using g_ge1[OF that] by (auto intro: order_trans[OF zero_le_one])
  obtain C where C: "eventually (\<lambda>X. prod g X \<le> C) (finite_subsets_at_top A)"
    using multipliable_on_imp_bounded_partial_sums[OF g] by blast

  have sum_g_le: "prod g X \<le> C" if X: "finite X" "X \<subseteq> A" for X
  proof -
    from C obtain X' where X':
      "finite X'" "X' \<subseteq> A" "\<And>Y. finite Y \<Longrightarrow> X' \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> prod g Y \<le> C"
      unfolding eventually_finite_subsets_at_top by metis
    have "prod g X \<le> prod g (X \<union> X')"
      by (intro prod_mono2) (use X X' g_ge1 g_nonneg in auto)
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
    proof (intro prod_mono conjI)
      fix x assume x: "x \<in> Y1"
      show "(\<Prod>y\<in>Y2 x. f (x, y)) \<le> g x"
      proof -
        have x': "x \<in> A" using x Y12_subset(1) by auto
        have lim: "(prod (\<lambda>y. f (x, y)) \<longlongrightarrow> g x) (finite_subsets_at_top (B x))"
          using f[OF x'] by (simp add: has_setprod_def)
        have "g x \<in> {prod (\<lambda>y. f (x, y)) (Y2 x)..}"
        proof (rule Lim_in_closed_set[OF closed_atLeast _ finite_subsets_at_top_neq_bot lim])
          show "\<forall>\<^sub>F X in finite_subsets_at_top (B x). prod (\<lambda>y. f (x, y)) X \<in> {prod (\<lambda>y. f (x, y)) (Y2 x)..}"
            unfolding eventually_finite_subsets_at_top
          proof (intro exI[of _ "Y2 x"] conjI allI impI)
            fix Z assume Z: "finite Z \<and> Y2 x \<subseteq> Z \<and> Z \<subseteq> B x"
            show "prod (\<lambda>y. f (x, y)) Z \<in> {prod (\<lambda>y. f (x, y)) (Y2 x)..}"
            proof (simp add: atLeast_def, rule prod_mono2)
              show "finite Z" "Y2 x \<subseteq> Z" using Z by auto
            next
              fix b assume "b \<in> Z - Y2 x"
              hence "b \<in> B x" using Z by auto
              thus "1 \<le> f (x, b)" using x' f_nonneg by auto
            next
              fix a assume "a \<in> Y2 x"
              hence "a \<in> B x" using Y12_subset by auto
              thus "0 \<le> f (x, a)" using x' f_nonneg by (meson order_trans zero_le_one)
            qed
          qed (use Y12_subset x in auto)
        qed
        thus ?thesis by simp
      qed
      show "\<And>i. i \<in> Y1 \<Longrightarrow> 0 \<le> (\<Prod>y\<in>Y2 i. f (i, y))"
        by (meson Y12_subset(1,2) f_nonneg order.trans prod_nonneg subset_iff zero_le_one)
    qed
    also have "\<dots> \<le> C"
      using Y12_subset sum_g_le by blast
    finally show ?thesis .
  qed

  hence "\<forall>\<^sub>F X in finite_subsets_at_top (Sigma A B). prod f X \<le> C"
    unfolding eventually_finite_subsets_at_top by auto
  thus ?thesis
    by (metis SigmaE f_nonneg nonneg_bounded_partial_sums_imp_multipliable_on)
qed

lemma multipliable_on_UnionI:
  fixes f :: "_ \<Rightarrow> 'a :: {linorder_topology, linordered_idom, topological_comm_monoid_mult,
                          conditionally_complete_linorder}"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> (f has_setprod g x) (B x)"
  assumes g: "g multipliable_on A"
  assumes f_nonneg: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> f y \<ge> (1 :: 'a)"
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
  fixes f :: "'a \<times> 'b \<Rightarrow> 'c :: real_normed_field"
  assumes sum1: "f multipliable_on (Sigma A B)"
  assumes sum2: "\<And>x. x \<in> A \<Longrightarrow> (\<lambda>y. f (x, y)) multipliable_on (B x)"
  shows   "(\<lambda>x. infprod (\<lambda>y. f (x, y)) (B x)) multipliable_on A"
  using assms unfolding multipliable_on_def
  by (smt (verit, del_insts) assms has_setprod_SigmaD has_setprod_cong has_setprod_infprod)

lemma multipliable_on_UnionD:
  fixes f :: "'a \<Rightarrow> 'c :: real_normed_field"
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
  fixes f :: "_ \<Rightarrow> 'a :: {linorder_topology, real_normed_field, topological_comm_monoid_mult,
                          conditionally_complete_linorder, linordered_idom}"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> (f has_setprod g x) (B x)"
  assumes f_nonneg: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> f y \<ge> 1"
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
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{comm_monoid_mult, semidom, topological_semigroup_mult, t2_space, uniform_space, uniform_topological_group_add}\<close>
  assumes multipliableAB: "(f has_setprod a) (Sigma A B)"
  assumes multipliableB: \<open>\<And>x. x\<in>A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_setprod (b x)) (B x)\<close>
  shows "(b has_setprod a) A"
  sorry


(* TODO from Manuel:
   Figure out how to generalise uniformly_convergent_prod_Cauchy, convergent_prod_Cauchy_iff.
   Might involve Cauchy filters, similarly to the proof of abs_summable_summable.

lemma uniformly_convergent_prod_Cauchy:
  fixes f :: "nat \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach}"
  assumes C: "\<And>x m. x \<in> A \<Longrightarrow> norm (\<Prod>k<m. f k x) \<le> C"
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>M. \<forall>x\<in>A. \<forall>m\<ge>M. \<forall>n\<ge>m. dist (\<Prod>k=m..n. f k x) 1 < e"
  shows   "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. f n x)"
proof (rule Cauchy_uniformly_convergent, rule uniformly_Cauchy_onI')
  fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0"
  define C' where "C' = max C 1"
  have C': "C' > 0"
    by (auto simp: C'_def)
  define \<delta> where "\<delta> = Min {2 / 3 * \<epsilon> / C', 1 / 2}"
  from \<epsilon> have "\<delta> > 0"
    using \<open>C' > 0\<close> by (auto simp: \<delta>_def)
  obtain M where M: "\<And>x m n. x \<in> A \<Longrightarrow> m \<ge> M \<Longrightarrow> n \<ge> m \<Longrightarrow> dist (\<Prod>k=m..n. f k x) 1 < \<delta>"
    using \<open>\<delta> > 0\<close> assms by fast

  show "\<exists>M. \<forall>x\<in>A. \<forall>m\<ge>M. \<forall>n>m. dist (\<Prod>k<m. f k x) (\<Prod>k<n. f k x) < \<epsilon>"
  proof (rule exI, intro ballI allI impI)
    fix x m n
    assume x: "x \<in> A" and mn: "M + 1 \<le> m" "m < n"
    show "dist (\<Prod>k<m. f k x) (\<Prod>k<n. f k x) < \<epsilon>"
    proof (cases "\<exists>k<m. f k x = 0")
      case True
      hence "(\<Prod>k<m. f k x) = 0" and "(\<Prod>k<n. f k x) = 0"
        using mn x by (auto intro!: prod_zero)
      thus ?thesis
        using \<epsilon> by simp
    next
      case False
      have *: "{..<n} = {..<m} \<union> {m..n-1}"
        using mn by auto
      have "dist (\<Prod>k<m. f k x) (\<Prod>k<n. f k x) = norm ((\<Prod>k<m. f k x) * ((\<Prod>k=m..n-1. f k x) - 1))"
        unfolding * by (subst prod.union_disjoint)
                       (use mn in \<open>auto simp: dist_norm algebra_simps norm_minus_commute\<close>)
      also have "\<dots> = (\<Prod>k<m. norm (f k x)) * dist (\<Prod>k=m..n-1. f k x) 1"
        by (simp add: norm_mult dist_norm prod_norm)
      also have "\<dots> < (\<Prod>k<m. norm (f k x)) * (2 / 3 * \<epsilon> / C')"
      proof (rule mult_strict_left_mono)
        show "dist (\<Prod>k = m..n - 1. f k x) 1 < 2 / 3 * \<epsilon> / C'"
          using M[of x m "n-1"] x mn unfolding \<delta>_def by fastforce
      qed (use False in \<open>auto intro!: prod_pos\<close>)
      also have "(\<Prod>k<m. norm (f k x)) = (\<Prod>k<M. norm (f k x)) * norm (\<Prod>k=M..<m. (f k x))"
      proof -
        have *: "{..<m} = {..<M} \<union> {M..<m}"
          using mn by auto
        show ?thesis
          unfolding * using mn by (subst prod.union_disjoint) (auto simp: prod_norm)
      qed
      also have "norm (\<Prod>k=M..<m. (f k x)) \<le> 3 / 2"
      proof -
        have "dist (\<Prod>k=M..m-1. f k x) 1 < \<delta>"
          using M[of x M "m-1"] x mn \<open>\<delta> > 0\<close> by auto
        also have "\<dots> \<le> 1 / 2"
          by (simp add: \<delta>_def)
        also have "{M..m-1} = {M..<m}"
          using mn by auto
        finally have "norm (\<Prod>k=M..<m. f k x) \<le> norm (1 :: 'b) + 1 / 2"
          by norm
        thus ?thesis
          by simp
      qed
      hence "(\<Prod>k<M. norm (f k x)) * norm (\<Prod>k = M..<m. f k x) * (2 / 3 * \<epsilon> / C') \<le>
             (\<Prod>k<M. norm (f k x)) * (3 / 2) * (2 / 3 * \<epsilon> / C')"
        using \<epsilon> C' by (intro mult_left_mono mult_right_mono prod_nonneg) auto
      also have "\<dots> \<le> C' * (3 / 2) * (2 / 3 * \<epsilon> / C')"
      proof (intro mult_right_mono)
        have "(\<Prod>k<M. norm (f k x)) \<le> C"
          using C[of x M] x by (simp add: prod_norm)
        also have "\<dots> \<le> C'"
          by (simp add: C'_def)
        finally show "(\<Prod>k<M. norm (f k x)) \<le> C'" .
      qed (use \<epsilon> C' in auto)
      finally show "dist (\<Prod>k<m. f k x) (\<Prod>k<n. f k x) < \<epsilon>"
        using \<open>C' > 0\<close> by (simp add: field_simps)
    qed
  qed
qed

*)


(* 
  TODO from Manuel: Proof is probably similar to abs_multipliable_on_iff_summable_on.
  Or take inspiration from uniformly_convergent_on_prod.
  But that requires the Cauchy theorems...
*)
lemma uniform_limit_prodinf:
  fixes f :: "nat \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach}"
  assumes cont: "\<And>n. continuous_on B (f n)"
  assumes A: "compact B"
  assumes conv_sum: "uniform_limit B (\<lambda>X y. \<Sum>x\<in>X. norm (f x y)) L (finite_subsets_at_top A)"
  shows   "uniform_limit B (\<lambda>X y. \<Prod>x\<in>X. 1 + f x y) (\<lambda>y. \<Prod>x\<in>X. 1 + f x y) (finite_subsets_at_top A)"
  sorry

lemma uniform_limit_prodinf':
  fixes f :: "nat \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach}"
  assumes cont: "\<And>n. continuous_on B (f n)"
  assumes A: "compact B"
  assumes conv_sum: "uniform_limit B (\<lambda>X y. \<Sum>x\<in>X. norm (f x y - 1)) L (finite_subsets_at_top A)"
  shows   "uniform_limit B (\<lambda>X y. \<Prod>x\<in>X. f x y) (\<lambda>y. \<Prod>x\<in>X. f x y) (finite_subsets_at_top A)"
proof -
  have "uniform_limit B (\<lambda>X y. \<Prod>x\<in>X. 1 + (f x y - 1)) (\<lambda>y. \<Prod>x\<in>X. 1 + (f x y - 1)) (finite_subsets_at_top A)"
    by (rule uniform_limit_prodinf) (use assms in \<open>auto intro!: continuous_intros\<close>)
  thus ?thesis
    by simp
qed
            


subsection \<open>Real numbers\<close>

text \<open>Most lemmas in the general property section already apply to real numbers.
      A few ones that are specific to reals are given here.\<close>

(*
  Contributed by Manuel: for real numbers, strong multipliability is equivalent to
  absolute multipliability. The same clearley does not hold for "normal" multipliability.

  The analogous statement also holds for complex numbers but is probably more difficult to
  prove there.
*)
lemma strongly_multipliable_on_iff_abs_multipliable_on_real:
  fixes f :: \<open>'a \<Rightarrow> real\<close>
  shows \<open>f strongly_multipliable_on A \<longleftrightarrow> f abs_multipliable_on A\<close>
proof
  assume *: "f strongly_multipliable_on A"
  then obtain B where B: "B \<subseteq> A" "finite B" "\<And>x. x \<in> A-B \<Longrightarrow> f x \<in> {0<..}"
    using strongly_multipliable_on_imp_nhds_1[OF *, of "{0<..}"] by auto
  have "f strongly_multipliable_on (A - B)"
    by (rule strongly_multipliable_on_Diff_finite) fact+
  moreover from B(3) have "f x \<noteq> 0" if "x \<in> A - B" for x
    using that by force
  ultimately obtain P where P: "(f has_setprod P) (A - B)" "P \<noteq> 0"
    by (subst (asm) strongly_multipliable_on_nonzero_iff) auto

  from P have "((\<lambda>x. ln (f x)) has_sum ln P) (A - B)"
    by (intro has_prod_imp_sums_ln_real)
  hence "(\<lambda>x. ln (f x)) summable_on (A - B)"
    using has_sum_imp_summable by blast
  hence "(\<lambda>x. ln (f x)) abs_summable_on (A - B)"
    by (subst (asm) summable_on_iff_abs_summable_on_real)
  hence "(\<lambda>x. exp (ln (f x))) abs_multipliable_on (A - B)"
    by (intro abs_multipliable_on_exp)
  also have "?this \<longleftrightarrow> f abs_multipliable_on (A - B)"
    by (intro abs_multipliable_on_cong) (use B in auto)
  finally have "f abs_multipliable_on (A - B \<union> B)"
    by (intro abs_multipliable_on_Un_disjoint) (use B in auto)
  also have "A - B \<union> B = A"
    using B by auto
  finally show "f abs_multipliable_on A" .
qed (use abs_multipliable_on_imp_strongly_multipliable_on in blast)

(*
  TODO from Manuel: This is a bit ad-hoc; not sure how useful it really is.
*)
lemma multipliable_on_iff_abs_multipliable_on_real:
  fixes f :: \<open>'a \<Rightarrow> real\<close>
  assumes fge1: \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 1\<close>
  shows \<open>f multipliable_on A \<longleftrightarrow> f abs_multipliable_on A\<close>
proof -
  have eq: \<open>1 + norm (f x - 1) = f x\<close> if \<open>x \<in> A\<close> for x
  proof -
    from fge1[OF that] have \<open>f x - 1 \<ge> 0\<close> by simp
    then show ?thesis by simp
  qed
  show ?thesis
    unfolding abs_multipliable_on_def
    using multipliable_on_cong[of A \<open>\<lambda>x. 1 + norm (f x - 1)\<close> f] eq by auto
qed

subsection \<open>Complex numbers\<close>


lemma strongly_multipliable_on_iff_abs_multipliable_on_complex:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>f strongly_multipliable_on A \<longleftrightarrow> f abs_multipliable_on A\<close>
(*
  Proof idea: right-to-left direction is trivial. For left-to-right, assume that f is strongly
  multipliable and w.l.o.g. f(x) \<noteq> 0 for all x. Then since \<Prod>f(x) converges to some P, \<Sum>ln(f(x)) 
  converges to ln(P) + 2*\<i>*pi*k for some k (this part might be a bit fiddly, but similar things exist
  already for has_prod, see below). But then \<Sum>ln(f(x)) is absolutely summable since summability
  and absolute summability coincide for complex numbers, and thereby exp(ln(f(x))) is
  absolutely multipliable.

  The main pain point here is to establish the convergence of \<Sum>ln(f(x)) since we might cross
  a bunch of branch cuts. It's not clear to make this formal. Some ideas might be drawn from
  the same proof for "convergent_prod", e.g. the lemma Ln_prodinf_complex.

theorem Ln_prodinf_complex:
  fixes z :: "nat \<Rightarrow> complex"
  assumes z: "\<And>j. z j \<noteq> 0" and \<xi>: "\<xi> \<noteq> 0"
  shows "((\<lambda>n. \<Prod>j\<le>n. z j) \<longlonglongrightarrow> \<xi>) \<longleftrightarrow> (\<exists>k. (\<lambda>n. (\<Sum>j\<le>n. Ln (z j))) \<longlonglongrightarrow> Ln \<xi> + of_int k * (of_real(2*pi) * \<i>))" (is "?lhs = ?rhs")

*)
  sorry

lemma has_setprod_cnj_iff[simp]: 
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>((\<lambda>x. cnj (f x)) has_setprod cnj a) M \<longleftrightarrow> (f has_setprod a) M\<close>
  using lim_cnj by (fastforce simp add: has_setprod_def)

lemma multipliable_on_cnj_iff[simp]:
  "(\<lambda>i. cnj (f i)) multipliable_on A \<longleftrightarrow> f multipliable_on A"
  by (metis complex_cnj_cnj multipliable_on_def has_setprod_cnj_iff)

lemma infprod_cnj[simp]: \<open>infprod (\<lambda>x. cnj (f x)) M = cnj (infprod f M)\<close>
  by (metis complex_cnj_one has_setprod_cnj_iff has_setprod_infprod infprodI
      infprod_not_exists multipliable_on_cnj_iff)

lemma has_setprod_Re:
  assumes "(f has_setprod a) M" and real: "\<And>x. x \<in> M \<Longrightarrow> f x \<in> \<real>"
  shows "((\<lambda>x. Re (f x)) has_setprod Re a) M"
proof -
  have eq: "\<forall>\<^sub>F X in finite_subsets_at_top M. prod (\<lambda>x. Re (f x)) X = Re (prod f X)"
    by (rule eventually_finite_subsets_at_top_weakI)
       (metis Re_prod_Reals real subset_iff)
  from assms(1) have "(prod f \<longlongrightarrow> a) (finite_subsets_at_top M)"
    by (simp add: has_setprod_def)
  then have "((\<lambda>X. Re (prod f X)) \<longlongrightarrow> Re a) (finite_subsets_at_top M)"
    by (rule tendsto_Re)
  then show ?thesis
    using eq unfolding has_setprod_def by (simp add: filterlim_cong)
qed

lemma infprod_Re:
  assumes "f multipliable_on M" and "\<And>x. x \<in> M \<Longrightarrow> f x \<in> \<real>"
  shows "infprod (\<lambda>x. Re (f x)) M = Re (infprod f M)"
  by (simp add: assms has_setprod_Re infprodI)

lemma multipliable_on_Re:
  assumes "f multipliable_on M" and "\<And>x. x \<in> M \<Longrightarrow> f x \<in> \<real>"
  shows "(\<lambda>x. Re (f x)) multipliable_on M"
  by (metis assms has_setprod_Re multipliable_on_def)

lemma has_setprod_Im:
  assumes "(f has_setprod a) M" and real: "\<And>x. x \<in> M \<Longrightarrow> f x \<in> \<real>" and "M \<noteq> {}"
  shows "((\<lambda>x. Im (f x)) has_setprod Im a) M"
proof -
  from \<open>M \<noteq> {}\<close> obtain m where "m \<in> M" by blast
  have eq: "\<forall>\<^sub>F X in finite_subsets_at_top M. prod (\<lambda>x. Im (f x)) X = Im (prod f X)"
    unfolding eventually_finite_subsets_at_top
  proof (intro exI[of _ "{m}"] conjI allI impI)
    show "finite {m}" "{m} \<subseteq> M" using \<open>m \<in> M\<close> by auto
  next
    fix X assume "finite X \<and> {m} \<subseteq> X \<and> X \<subseteq> M"
    then have "finite X" "X \<subseteq> M" "X \<noteq> {}" by auto
    have "Im (f x) = 0" if "x \<in> X" for x
      using real \<open>X \<subseteq> M\<close> that by (auto simp: complex_is_Real_iff subset_iff)
    then have "prod (\<lambda>x. Im (f x)) X = prod (\<lambda>x. (0::real)) X"
      by (intro prod.cong) auto
    also have "\<dots> = 0"
      using \<open>finite X\<close> \<open>X \<noteq> {}\<close> by (intro prod_zero) auto
    finally have lhs: "prod (\<lambda>x. Im (f x)) X = 0" .
    have "prod f X \<in> \<real>"
      using real \<open>X \<subseteq> M\<close> by (intro prod_in_Reals) (auto simp: subset_iff)
    then have "Im (prod f X) = 0"
      by (simp add: complex_is_Real_iff)
    with lhs show "prod (\<lambda>x. Im (f x)) X = Im (prod f X)" by simp
  qed
  from assms(1) have "(prod f \<longlongrightarrow> a) (finite_subsets_at_top M)"
    by (simp add: has_setprod_def)
  then have "((\<lambda>X. Im (prod f X)) \<longlongrightarrow> Im a) (finite_subsets_at_top M)"
    by (rule tendsto_Im)
  then show ?thesis
    unfolding has_setprod_def using eq tendsto_cong by fastforce
qed


lemma infprod_Im:
  assumes "f multipliable_on M" and "\<And>x. x \<in> M \<Longrightarrow> f x \<in> \<real>" and "M \<noteq> {}"
  shows "infprod (\<lambda>x. Im (f x)) M = Im (infprod f M)"
  by (simp add: assms has_setprod_Im infprodI)

lemma multipliable_on_Im:
  assumes "f multipliable_on M" and "\<And>x. x \<in> M \<Longrightarrow> f x \<in> \<real>" and "M \<noteq> {}"
  shows "(\<lambda>x. Im (f x)) multipliable_on M"
  by (metis assms has_setprod_Im multipliable_on_def)




(* TODO: statement likely needs fixing (norm(f x) need not be \<ge> 1)
lemma abs_multipliable_on_comparison_test':
  assumes "g multipliable_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (f x) \<le> g x"
  shows   "(\<lambda>x. norm (f x)) multipliable_on A"
*)


(* TODO: requires multipliable_Suc_iff, norm_multipliable_imp_has_setprod, multipliable_geometric
lemma has_setprod_geometric_from_1:
  fixes z :: "'a :: {real_normed_field, banach}"
  assumes "norm z < 1"
  shows   "((\<lambda>n. z ^ n) has_setprod (z / (1 - z))) {1..}"
*)


(*
lemma has_setprod_divide_const:
  fixes f :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, field, semiring_0}"
  shows "(f has_setprod S) A \<Longrightarrow> ((\<lambda>x. f x / c) has_setprod (S / c)) A"
  using has_setprod_cmult_right[of f A S "inverse c"] by (simp add: field_simps)

lemma has_setprod_uminusI:
  fixes f :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, ring_1}"
  shows "(f has_setprod S) A \<Longrightarrow> ((\<lambda>x. -f x) has_setprod (-S)) A"
  using has_setprod_cmult_right[of f A S "-1"] by simp
*)

lemma multipliable_countable_real:
  fixes f :: \<open>'a \<Rightarrow> real\<close>
  assumes \<open>f strongly_multipliable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 1}\<close>
  using assms by (rule multipliable_countable)

end
