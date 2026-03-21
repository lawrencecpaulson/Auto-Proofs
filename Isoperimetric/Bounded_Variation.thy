theory Bounded_Variation
  imports "HOL-Analysis.Analysis"
begin

text \<open>
  Bounded variation and vector variation for functions @{typ "real \<Rightarrow> 'a::euclidean_space"},
  following HOL Light's @{text "Multivariate/integration.ml"} (lines 8660--19100).

  HOL Light works with @{text "real^1 \<Rightarrow> real^N"} and defines bounded variation via
  set variation of the increment function. We adapt this to Isabelle's @{typ real}
  domain directly.
\<close>

section \<open>Set variation\<close>

definition set_variation :: "real set \<Rightarrow> (real set \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real" where
  "set_variation s f = Sup {sum d (\<lambda>k. norm (f k)) | d. \<exists>t. d division_of t \<and> t \<subseteq> s}"

definition has_bounded_setvariation_on ::
  "(real set \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real set \<Rightarrow> bool" where
  "has_bounded_setvariation_on f s \<longleftrightarrow>
    (\<exists>B. \<forall>d t. d division_of t \<and> t \<subseteq> s \<longrightarrow> sum d (\<lambda>k. norm (f k)) \<le> B)"

section \<open>Bounded variation for functions\<close>

definition has_bounded_variation_on ::
  "(real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real set \<Rightarrow> bool" where
  "has_bounded_variation_on f s \<longleftrightarrow>
    has_bounded_setvariation_on (\<lambda>k. f (Sup k) - f (Inf k)) s"

definition vector_variation :: "real set \<Rightarrow> (real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real" where
  "vector_variation s f = set_variation s (\<lambda>k. f (Sup k) - f (Inf k))"

subsection \<open>Basic properties\<close>

lemma has_bounded_variation_on_interval:
  "has_bounded_variation_on f {a..b} \<longleftrightarrow>
    (\<exists>B. \<forall>d. d division_of {a..b} \<longrightarrow>
      (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> B)"
  sorry

lemma vector_variation_on_interval:
  "vector_variation {a..b} f =
    Sup {(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) | d. d division_of {a..b}}"
  sorry

lemma vector_variation_pos_le:
  "has_bounded_variation_on f {a..b} \<Longrightarrow> 0 \<le> vector_variation {a..b} f"
  sorry

lemma vector_variation_ge_norm_function:
  assumes "has_bounded_variation_on f {a..b}" "x \<in> {a..b}" "y \<in> {a..b}"
  shows "norm (f x - f y) \<le> vector_variation {a..b} f"
  sorry

lemma vector_variation_const_eq:
  assumes "has_bounded_variation_on f {a..b}" "is_interval {a..b}"
  shows "vector_variation {a..b} f = 0 \<longleftrightarrow> (\<exists>c. \<forall>t \<in> {a..b}. f t = c)"
  sorry

lemma vector_variation_on_null:
  "content {a..b} = 0 \<Longrightarrow> vector_variation {a..b} f = 0"
  sorry

lemma vector_variation_monotone:
  assumes "has_bounded_variation_on f {a..b}" "{c..d} \<subseteq> {a..b}"
  shows "vector_variation {c..d} f \<le> vector_variation {a..b} f"
  sorry

lemma vector_variation_combine:
  assumes "has_bounded_variation_on f {a..b}" "c \<in> {a..b}"
  shows "vector_variation {a..b} f =
    vector_variation {a..c} f + vector_variation {c..b} f"
  sorry

subsection \<open>Closure and subset properties\<close>

lemma has_bounded_variation_on_subset:
  "has_bounded_variation_on f s \<Longrightarrow> t \<subseteq> s \<Longrightarrow> has_bounded_variation_on f t"
  sorry

lemma has_bounded_variation_on_const:
  "has_bounded_variation_on (\<lambda>x. c) s"
  sorry

lemma has_bounded_variation_on_cmul:
  "has_bounded_variation_on f s \<Longrightarrow> has_bounded_variation_on (\<lambda>x. a *\<^sub>R f x) s"
  sorry

lemma has_bounded_variation_on_neg:
  "has_bounded_variation_on f s \<Longrightarrow> has_bounded_variation_on (\<lambda>x. - f x) s"
  sorry

lemma has_bounded_variation_on_add:
  "has_bounded_variation_on f s \<Longrightarrow> has_bounded_variation_on g s \<Longrightarrow>
    has_bounded_variation_on (\<lambda>x. f x + g x) s"
  sorry

lemma has_bounded_variation_on_sub:
  "has_bounded_variation_on f s \<Longrightarrow> has_bounded_variation_on g s \<Longrightarrow>
    has_bounded_variation_on (\<lambda>x. f x - g x) s"
  sorry

lemma has_bounded_variation_on_norm:
  "has_bounded_variation_on f s \<Longrightarrow>
    has_bounded_variation_on (\<lambda>x. norm (f x) *\<^sub>R e) s"
  sorry

subsection \<open>Composition and monotonicity\<close>

lemma has_bounded_variation_compose_increasing:
  assumes "has_bounded_variation_on f {a..b}"
    and "\<And>x y. x \<in> {c..d} \<Longrightarrow> y \<in> {c..d} \<Longrightarrow> x \<le> y \<Longrightarrow> g x \<le> g y"
    and "g ` {c..d} \<subseteq> {a..b}"
  shows "has_bounded_variation_on (f \<circ> g) {c..d}"
  sorry

lemma has_bounded_variation_on_compose_linear:
  assumes "has_bounded_variation_on f s" "linear h"
  shows "has_bounded_variation_on (h \<circ> f) s"
  sorry

lemma lipschitz_imp_has_bounded_variation:
  assumes "bounded s"
    and "\<And>x y. x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> norm (f x - f y) \<le> B * norm (x - y)"
  shows "has_bounded_variation_on f s"
  sorry

lemma lipschitz_vector_variation:
  assumes "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> norm (f x - f y) \<le> B * \<bar>x - y\<bar>"
  shows "vector_variation {a..b} f \<le> B * (b - a)"
  sorry

subsection \<open>Bounded variation implies bounded\<close>

lemma has_bounded_variation_on_imp_bounded:
  "has_bounded_variation_on f {a..b} \<Longrightarrow> bounded (f ` {a..b})"
  sorry

subsection \<open>Increasing/decreasing functions\<close>

lemma increasing_bounded_variation:
  assumes "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> x \<le> y \<Longrightarrow> drop (f x) \<le> drop (f y)"
  shows "has_bounded_variation_on f {a..b}"
  sorry

lemma increasing_vector_variation:
  assumes "\<And>x y. x \<in> {a..b} \<Longrightarrow> y \<in> {a..b} \<Longrightarrow> x \<le> y \<Longrightarrow> drop (f x) \<le> drop (f y)"
    and "a \<le> b"
  shows "vector_variation {a..b} f = norm (f b - f a)"
  sorry

subsection \<open>Continuity of vector variation\<close>

lemma vector_variation_continuous:
  assumes "f continuous_on {a..b}" "has_bounded_variation_on f {a..b}"
  shows "(\<lambda>x. vector_variation {a..x} f) continuous_on {a..b}"
  sorry

lemma vector_variation_minus_function_monotone:
  assumes "has_bounded_variation_on f {a..b}" "x \<in> {a..b}" "y \<in> {a..b}" "x \<le> y"
  shows "norm (f y - f x) \<le> vector_variation {x..y} f"
    and "vector_variation {a..x} f - norm (f x - f a) \<le>
      vector_variation {a..y} f - norm (f y - f a)"
  sorry sorry

subsection \<open>Factoring through variation\<close>

lemma factor_continuous_through_variation:
  assumes "a \<le> b" "f continuous_on {a..b}"
    "has_bounded_variation_on f {a..b}"
    "vector_variation {a..b} f = l"
  shows "\<exists>g. (\<forall>x \<in> {a..b}. f x = g (vector_variation {a..x} f)) \<and>
    g continuous_on {0..l} \<and>
    (\<forall>u \<in> {0..l}. \<forall>v \<in> {0..l}. dist (g u) (g v) \<le> dist u v) \<and>
    has_bounded_variation_on g {0..l} \<and>
    (\<lambda>x. vector_variation {a..x} f) ` {a..b} = {0..l} \<and>
    g ` {0..l} = f ` {a..b} \<and>
    (\<forall>x \<in> {0..l}. vector_variation {0..x} g = x)"
  sorry

end
