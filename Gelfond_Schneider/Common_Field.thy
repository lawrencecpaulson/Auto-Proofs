(*  Title:      Gelfond_Schneider/Common_Field.thy
    Author:     OpenAI Codex

Common-field packaging for the standalone Gelfond-Schneider route.  This
isolates the primitive-element reduction over the rational subfield of
complex numbers: any algebraic triple a, b, w lives in one simple extension
Q(theta), and hence admits power-basis coordinates over Q.
*)

theory Common_Field
  imports
    GS_Preliminaries
    "HOL-New_Algebra.Finite_Generated_Extension"
    "HOL-New_Algebra.Primitive_Element"
    "HOL-New_Algebra.Galois_Normality"
begin

section \<open>Rational Common Fields\<close>

lemma algebraic_imp_algebraic_over_Rats:
  fixes x :: complex
  assumes alg: "algebraic x"
  shows "algebraic_over (\<rat> :: complex set) x"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  interpret Q: Subfield "(\<rat> :: complex set)"
    by (rule sfQ)
  obtain p :: "int poly" where px: "ipoly p x = 0" and p0: "p \<noteq> 0"
    using alg unfolding algebraic_altdef_ipoly by blast
  have pR: "of_int_poly p \<in> poly_over (\<rat> :: complex set)"
    by (auto simp: poly_over_def)
  have root: "poly (of_int_poly p) x = 0"
    using px by simp
  show ?thesis
    unfolding algebraic_over_def
    by (intro bexI[of _ "of_int_poly p"]) (use pR p0 root in auto)
qed

theorem exists_finite_rational_tower_of_algebraic_triple:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains L where
      "finite_subfield_tower (\<rat> :: complex set) L"
    and "(\<rat> :: complex set) \<subseteq> L"
    and "a \<in> L"
    and "b \<in> L"
    and "w \<in> L"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have finS: "finite ({a, b, w} :: complex set)"
    by simp
  have algS: "algebraic_over (\<rat> :: complex set) x" if "x \<in> ({a, b, w} :: complex set)" for x
    using assms that by (auto intro: algebraic_imp_algebraic_over_Rats)
  obtain L where
      T: "finite_subfield_tower (\<rat> :: complex set) L"
    and KL: "(\<rat> :: complex set) \<subseteq> L"
    and SL: "({a, b, w} :: complex set) \<subseteq> L"
    using exists_finite_subfield_tower[OF sfQ finS algS] by blast
  show thesis
    by (rule that[OF T KL]) (use SL in auto)
qed

theorem exists_primitive_rational_common_field_of_algebraic_triple:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains \<theta> where
      "a \<in> eval_img (\<rat> :: complex set) \<theta>"
    and "b \<in> eval_img (\<rat> :: complex set) \<theta>"
    and "w \<in> eval_img (\<rat> :: complex set) \<theta>"
    and "algebraic_over (\<rat> :: complex set) \<theta>"
    and "finite_subfield_tower (\<rat> :: complex set) (eval_img (\<rat> :: complex set) \<theta>)"
proof -
  obtain L where
      T: "finite_subfield_tower (\<rat> :: complex set) L"
    and KL: "(\<rat> :: complex set) \<subseteq> L"
    and aL: "a \<in> L"
    and bL: "b \<in> L"
    and wL: "w \<in> L"
    by (rule exists_finite_rational_tower_of_algebraic_triple[OF alg_a alg_b alg_w])
  interpret T: finite_subfield_tower "\<rat>" L by fact
  have sep: "separable_extension L (\<rat> :: complex set)"
    by (rule complex_extension_separable[OF complex_subfield_Rats])
  obtain \<theta> where \<theta>L: "\<theta> \<in> L"
    and prim: "primitive_element (\<rat> :: complex set) L \<theta>"
    using finite_separable_extension_is_simple[OF T sep] by blast
  have L_def: "L = eval_img (\<rat> :: complex set) \<theta>"
    by (rule primitive_elementD[OF prim])
  have alg_theta: "algebraic_over (\<rat> :: complex set) \<theta>"
    by (rule T.finite_extension_algebraic[OF \<theta>L])
  have T\<theta>: "finite_subfield_tower (\<rat> :: complex set) (eval_img (\<rat> :: complex set) \<theta>)"
    using T L_def by simp
  show thesis
    by (rule that[OF _ _ _ alg_theta T\<theta>]) (use aL bL wL L_def in auto)
qed

theorem exists_primitive_rational_common_field_coordinates_of_algebraic_triple:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains \<theta> d ca cb cw where
      "d = ext_degree (\<rat> :: complex set) \<theta>"
    and "d > 0"
    and "(\<forall>i<d. ca i \<in> (\<rat> :: complex set))"
    and "a = (\<Sum>i<d. ca i * \<theta> ^ i)"
    and "(\<forall>i<d. cb i \<in> (\<rat> :: complex set))"
    and "b = (\<Sum>i<d. cb i * \<theta> ^ i)"
    and "(\<forall>i<d. cw i \<in> (\<rat> :: complex set))"
    and "w = (\<Sum>i<d. cw i * \<theta> ^ i)"
proof -
  obtain \<theta> where
      aE: "a \<in> eval_img (\<rat> :: complex set) \<theta>"
    and bE: "b \<in> eval_img (\<rat> :: complex set) \<theta>"
    and wE: "w \<in> eval_img (\<rat> :: complex set) \<theta>"
    and alg_theta: "algebraic_over (\<rat> :: complex set) \<theta>"
    and _ : "finite_subfield_tower (\<rat> :: complex set) (eval_img (\<rat> :: complex set) \<theta>)"
    by (rule exists_primitive_rational_common_field_of_algebraic_triple[OF alg_a alg_b alg_w])
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  define d where "d = ext_degree (\<rat> :: complex set) \<theta>"
  obtain ca where ca:
      "\<forall>i<d. ca i \<in> (\<rat> :: complex set)"
      "a = (\<Sum>i<d. ca i * \<theta> ^ i)"
    using Subfield.power_basis_span[OF sfQ alg_theta aE]
    by (auto simp: d_def)
  obtain cb where cb:
      "\<forall>i<d. cb i \<in> (\<rat> :: complex set)"
      "b = (\<Sum>i<d. cb i * \<theta> ^ i)"
    using Subfield.power_basis_span[OF sfQ alg_theta bE]
    by (auto simp: d_def)
  obtain cw where cw:
      "\<forall>i<d. cw i \<in> (\<rat> :: complex set)"
      "w = (\<Sum>i<d. cw i * \<theta> ^ i)"
    using Subfield.power_basis_span[OF sfQ alg_theta wE]
    by (auto simp: d_def)
  have dpos: "d > 0"
    unfolding d_def by (rule Subfield.ext_degree_pos[OF sfQ alg_theta])
  show thesis
    by (rule that[OF d_def dpos ca(1) ca(2) cb(1) cb(2) cw(1) cw(2)])
qed


section \<open>Simple extension scaling\<close>

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
