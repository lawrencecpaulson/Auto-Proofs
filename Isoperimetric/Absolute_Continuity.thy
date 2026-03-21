theory Absolute_Continuity
  imports Bounded_Variation
begin

text \<open>
  Absolute continuity for functions @{typ "real \<Rightarrow> 'a::euclidean_space"},
  following HOL Light's @{text "Multivariate/integration.ml"} (lines 22442--23825)
  and the fundamental theorem of calculus for absolutely continuous functions
  from @{text "Multivariate/measure.ml"} (line 24882).

  In HOL Light, @{text "absolutely_continuous_on"} is defined via
  @{text "absolutely_setcontinuous_on"} applied to the increment function.
  We give an equivalent direct \<open>\<epsilon>\<close>-\<open>\<delta>\<close> formulation.
\<close>

section \<open>Absolute set-continuity\<close>

definition absolutely_setcontinuous_on ::
  "(real set \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real set \<Rightarrow> bool" where
  "absolutely_setcontinuous_on f s \<longleftrightarrow>
    (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> s \<and>
      (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow> (\<Sum>k\<in>d. norm (f k)) < \<epsilon>)"

section \<open>Absolute continuity for functions\<close>

definition absolutely_continuous_on ::
  "(real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real set \<Rightarrow> bool" where
  "absolutely_continuous_on f s \<longleftrightarrow>
    absolutely_setcontinuous_on (\<lambda>k. f (Sup k) - f (Inf k)) s"

subsection \<open>Basic properties\<close>

lemma absolutely_continuous_on_eq:
  "\<lbrakk>\<And>x. x \<in> s \<Longrightarrow> f x = g x; absolutely_continuous_on f s\<rbrakk> \<Longrightarrow>
    absolutely_continuous_on g s"
  sorry

lemma absolutely_continuous_on_subset:
  "absolutely_continuous_on f s \<Longrightarrow> t \<subseteq> s \<Longrightarrow> absolutely_continuous_on f t"
  sorry

lemma absolutely_continuous_on_const:
  "absolutely_continuous_on (\<lambda>x. c) s"
  sorry

lemma absolutely_continuous_on_cmul:
  "absolutely_continuous_on f s \<Longrightarrow> absolutely_continuous_on (\<lambda>x. a *\<^sub>R f x) s"
  sorry

lemma absolutely_continuous_on_neg:
  "absolutely_continuous_on f s \<Longrightarrow> absolutely_continuous_on (\<lambda>x. - f x) s"
  sorry

lemma absolutely_continuous_on_add:
  "absolutely_continuous_on f s \<Longrightarrow> absolutely_continuous_on g s \<Longrightarrow>
    absolutely_continuous_on (\<lambda>x. f x + g x) s"
  sorry

lemma absolutely_continuous_on_sub:
  "absolutely_continuous_on f s \<Longrightarrow> absolutely_continuous_on g s \<Longrightarrow>
    absolutely_continuous_on (\<lambda>x. f x - g x) s"
  sorry

lemma absolutely_continuous_on_norm:
  "absolutely_continuous_on f s \<Longrightarrow>
    absolutely_continuous_on (\<lambda>x. norm (f x) *\<^sub>R e) s"
  sorry

lemma absolutely_continuous_on_compose_linear:
  "absolutely_continuous_on f s \<Longrightarrow> linear h \<Longrightarrow>
    absolutely_continuous_on (h \<circ> f) s"
  sorry

lemma absolutely_continuous_on_null:
  "content {a..b} = 0 \<Longrightarrow> absolutely_continuous_on f {a..b}"
  sorry

lemma absolutely_continuous_on_id:
  "absolutely_continuous_on id {a..b}"
  sorry

subsection \<open>Relationship to bounded variation and continuity\<close>

lemma absolutely_continuous_on_imp_continuous:
  "absolutely_continuous_on f s \<Longrightarrow> f continuous_on s"
  sorry

lemma absolutely_continuous_on_imp_has_bounded_variation_on:
  "absolutely_continuous_on f {a..b} \<Longrightarrow> has_bounded_variation_on f {a..b}"
  sorry

lemma lipschitz_imp_absolutely_continuous:
  assumes "\<And>x y. x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> norm (f x - f y) \<le> B * \<bar>x - y\<bar>"
  shows "absolutely_continuous_on f s"
  sorry

subsection \<open>Combining intervals\<close>

lemma absolutely_continuous_on_combine:
  assumes "absolutely_continuous_on f {a..c}"
    "absolutely_continuous_on f {c..b}" "a \<le> c" "c \<le> b"
  shows "absolutely_continuous_on f {a..b}"
  sorry

lemma absolutely_continuous_on_division:
  assumes "\<And>k. k \<in> d \<Longrightarrow> absolutely_continuous_on f k"
    "d division_of {a..b}"
  shows "absolutely_continuous_on f {a..b}"
  sorry

subsection \<open>Bilinear and product\<close>

lemma absolutely_continuous_on_bilinear:
  assumes "absolutely_continuous_on f {a..b}"
    "absolutely_continuous_on g {a..b}" "bounded_bilinear h"
  shows "absolutely_continuous_on (\<lambda>x. h (f x) (g x)) {a..b}"
  sorry

lemma absolutely_continuous_on_mul:
  assumes "absolutely_continuous_on f {a..b}"
    "absolutely_continuous_on g {a..b}"
  shows "absolutely_continuous_on (\<lambda>x. f x * g x) {a..(b::real)}"
  sorry

subsection \<open>Fundamental theorem of calculus\<close>

theorem fundamental_theorem_of_calculus_absolutely_continuous:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "negligible S" "a \<le> b"
    "absolutely_continuous_on f {a..b}"
    "\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})"
  shows "(f' has_integral (f b - f a)) {a..b}"
  sorry

subsection \<open>Closure and interior\<close>

lemma absolutely_continuous_on_closure:
  assumes "absolutely_continuous_on f (interior {a..b})"
    "f continuous_on {a..b}"
  shows "absolutely_continuous_on f {a..b}"
  sorry

end
