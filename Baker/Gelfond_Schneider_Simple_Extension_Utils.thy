(*  Title:      Baker/Gelfond_Schneider_Simple_Extension_Utils.thy
    Author:     OpenAI Codex

Utility lemmas for the simple-extension route to the standalone
Gelfond-Schneider theorem.  The key observation is that rescaling a primitive
generator by a non-zero base-field element preserves both algebraicity and the
generated simple field.
*)

theory Gelfond_Schneider_Simple_Extension_Utils
  imports Gelfond_Schneider_Common_Field
begin

context Subfield
begin

lemma algebraic_over_mult_of_in_field:
  assumes alg: "algebraic_over K a"
    and cK: "c \<in> K"
  shows "algebraic_over K (c * a)"
proof -
  interpret Alg: Subfield "algebraic_elements K"
    by (rule subfield_algebraic_elements[OF Subfield_axioms])
  have cA: "c \<in> algebraic_elements K"
    using algebraic_over_self[OF cK] by (simp add: algebraic_elements_def)
  have aA: "a \<in> algebraic_elements K"
    using alg by (simp add: algebraic_elements_def)
  have "c * a \<in> algebraic_elements K"
    by (rule Alg.mult_closed[OF cA aA])
  then show ?thesis
    by (simp add: algebraic_elements_def)
qed

lemma eval_img_scale_eq:
  assumes alg: "algebraic_over K a"
    and cK: "c \<in> K"
    and cnz: "c \<noteq> 0"
  shows "eval_img K (c * a) = eval_img K a"
proof -
  have alg_ca: "algebraic_over K (c * a)"
    by (rule algebraic_over_mult_of_in_field[OF alg cK])
  have gen_eq: "generate_field (K \<union> {c * a}) = generate_field (K \<union> {a})"
  proof (rule antisym)
    interpret G: Subfield "generate_field (K \<union> {a})"
      by (rule subfield_generate_field)
    have cG: "c \<in> generate_field (K \<union> {a})"
      using cK by (auto intro: generate_field_base)
    have aG: "a \<in> generate_field (K \<union> {a})"
      by (auto intro: generate_field_base)
    have caG: "c * a \<in> generate_field (K \<union> {a})"
      by (rule G.mult_closed[OF cG aG])
    have "K \<union> {c * a} \<subseteq> generate_field (K \<union> {a})"
      using caG by (auto intro: generate_field_base)
    then show "generate_field (K \<union> {c * a}) \<subseteq> generate_field (K \<union> {a})"
      by (rule generate_field_least[OF subfield_generate_field])
  next
    interpret G: Subfield "generate_field (K \<union> {c * a})"
      by (rule subfield_generate_field)
    have cG: "c \<in> generate_field (K \<union> {c * a})"
      using cK by (auto intro: generate_field_base)
    have caG: "c * a \<in> generate_field (K \<union> {c * a})"
      by (auto intro: generate_field_base)
    have cinvG: "inverse c \<in> generate_field (K \<union> {c * a})"
      by (rule G.inverse_closed[OF cG])
    have aG: "a \<in> generate_field (K \<union> {c * a})"
    proof -
      have "a = inverse c * (c * a)"
        using cnz by (simp add: field_simps)
      also have "\<dots> \<in> generate_field (K \<union> {c * a})"
        by (rule G.mult_closed[OF cinvG caG])
      finally show ?thesis .
    qed
    have "K \<union> {a} \<subseteq> generate_field (K \<union> {c * a})"
      using aG cK by (auto intro: generate_field_base)
    then show "generate_field (K \<union> {a}) \<subseteq> generate_field (K \<union> {c * a})"
      by (rule generate_field_least[OF subfield_generate_field])
  qed
  have "eval_img K (c * a) = generate_field (K \<union> {c * a})"
    by (rule eval_img_eq_generate_field[OF alg_ca])
  also have "\<dots> = generate_field (K \<union> {a})"
    by (rule gen_eq)
  also have "\<dots> = eval_img K a"
    by (rule sym, rule eval_img_eq_generate_field[OF alg])
  finally show ?thesis .
qed

lemma ext_degree_eq_of_eval_img_eq:
  assumes alg_a: "algebraic_over K a"
    and alg_b: "algebraic_over K b"
    and eq: "eval_img K a = eval_img K b"
  shows "ext_degree K a = ext_degree K b"
proof -
  have fin: "finite_subfield_tower K (eval_img K a)"
    by (rule finite_subfield_tower_simple[OF Subfield_axioms alg_a])
  interpret T: finite_subfield_tower K "eval_img K a"
    by (rule fin)
  have prim_a: "primitive_element K (eval_img K a) a"
    by (rule primitive_elementI) simp
  have prim_b: "primitive_element K (eval_img K a) b"
    using eq by (simp add: primitive_element_def)
  have deg_a: "T.extension_degree = ext_degree K a"
    by (rule T.primitive_element_degree[OF prim_a])
  have deg_b: "T.extension_degree = ext_degree K b"
    by (rule T.primitive_element_degree[OF prim_b])
  show ?thesis
    using deg_a deg_b by simp
qed

lemma ext_degree_scale_eq:
  assumes alg: "algebraic_over K a"
    and cK: "c \<in> K"
    and cnz: "c \<noteq> 0"
  shows "ext_degree K (c * a) = ext_degree K a"
proof (rule ext_degree_eq_of_eval_img_eq)
  show "algebraic_over K (c * a)"
    by (rule algebraic_over_mult_of_in_field[OF alg cK])
  show "algebraic_over K a"
    by (rule alg)
  show "eval_img K (c * a) = eval_img K a"
    by (rule eval_img_scale_eq[OF alg cK cnz])
qed

end

end
