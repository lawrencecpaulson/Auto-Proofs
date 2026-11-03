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
  shows "algebraic_over \<rat> x"
proof -
  obtain p :: "int poly" where px: "ipoly p x = 0" and p0: "p \<noteq> 0"
    using alg unfolding algebraic_altdef_ipoly by blast
  have pR: "of_int_poly p \<in> poly_over \<rat>"
    by (auto simp: poly_over_def)
  show ?thesis
    using algebraic_over_def p0 pR px by blast
qed

theorem exists_finite_rational_tower_of_algebraic_triple:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains L where
      "finite_subfield_tower \<rat> L"
    and "\<rat> \<subseteq> L"
    and "a \<in> L"
    and "b \<in> L"
    and "w \<in> L"
proof -
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  have finS: "finite {a,b,w}"
    by simp
  have algS: "algebraic_over \<rat> x" if "x \<in> {a,b,w}" for x
    using assms that by (auto intro: algebraic_imp_algebraic_over_Rats)
  obtain L where "finite_subfield_tower \<rat> L" "\<rat> \<subseteq> L" "{a,b,w} \<subseteq> L"
    using exists_finite_subfield_tower[OF sfQ finS algS] by blast
  then show thesis
    using that by auto
qed

theorem exists_primitive_rational_common_field_of_algebraic_triple:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains \<theta> where "a \<in> eval_img \<rat> \<theta>"
    and "b \<in> eval_img \<rat> \<theta>"
    and "w \<in> eval_img \<rat> \<theta>"
    and "algebraic_over \<rat> \<theta>"
    and "finite_subfield_tower \<rat> (eval_img \<rat> \<theta>)"
proof -
  obtain L where T: "finite_subfield_tower \<rat> L"
    and KL: "\<rat> \<subseteq> L" and aL: "a \<in> L" and bL: "b \<in> L" and wL: "w \<in> L"
    by (rule exists_finite_rational_tower_of_algebraic_triple[OF alg_a alg_b alg_w])
  interpret T: finite_subfield_tower "\<rat>" L by fact
  have sep: "separable_extension L \<rat>"
    by (rule complex_extension_separable[OF complex_subfield_Rats])
  obtain \<theta> where \<theta>L: "\<theta> \<in> L" and L_def: "L = eval_img \<rat> \<theta>"
           and prim: "primitive_element \<rat> L \<theta>"
    using finite_separable_extension_is_simple[OF T sep] primitive_elementD by blast
  have alg_theta: "algebraic_over \<rat> \<theta>"
    by (rule T.finite_extension_algebraic[OF \<theta>L])
  have "finite_subfield_tower \<rat> (eval_img \<rat> \<theta>)"
    using T L_def by simp
  then show thesis
    using L_def aL alg_theta bL that wL by blast
qed

locale rational_power_basis_coordinates =
  fixes D :: nat
    and eta :: complex
    and ca cb cw :: "nat \<Rightarrow> complex"
    and a b w :: complex
  assumes ca_rat: "\<forall>i<D. ca i \<in> \<rat>"
    and a_eq: "a = (\<Sum>i<D. ca i * eta ^ i)"
    and cb_rat: "\<forall>i<D. cb i \<in> \<rat>"
    and b_eq: "b = (\<Sum>i<D. cb i * eta ^ i)"
    and cw_rat: "\<forall>i<D. cw i \<in> \<rat>"
    and w_eq: "w = (\<Sum>i<D. cw i * eta ^ i)"

theorem exists_primitive_rational_common_field_coordinates_of_algebraic_triple:
  fixes a b w :: complex
  assumes alg_a: "algebraic a"
    and alg_b: "algebraic b"
    and alg_w: "algebraic w"
  obtains \<theta> d ca cb cw where "d = ext_degree \<rat> \<theta>"
    and "d > 0"
    and "rational_power_basis_coordinates d \<theta> ca cb cw a b w"
proof -
  obtain \<theta> where aE: "a \<in> eval_img \<rat> \<theta>"
    and bE: "b \<in> eval_img \<rat> \<theta>"
    and wE: "w \<in> eval_img \<rat> \<theta>"
    and alg_theta: "algebraic_over \<rat> \<theta>"
    by (rule exists_primitive_rational_common_field_of_algebraic_triple[OF alg_a alg_b alg_w])
  have sfQ: "Subfield (\<rat> :: complex set)"
    using complex_subfield_Rats by (simp add: complex_subfield_iff_subfield)
  define d where "d \<equiv> ext_degree \<rat> \<theta>"
  obtain ca where ca: "\<forall>i<d. ca i \<in> \<rat>" "a = (\<Sum>i<d. ca i * \<theta> ^ i)"
    using Subfield.power_basis_span[OF sfQ alg_theta aE]
    by (auto simp: d_def)
  obtain cb where cb: "\<forall>i<d. cb i \<in> \<rat>" "b = (\<Sum>i<d. cb i * \<theta> ^ i)"
    using Subfield.power_basis_span[OF sfQ alg_theta bE]
    by (auto simp: d_def)
  obtain cw where cw: "\<forall>i<d. cw i \<in> \<rat>" "w = (\<Sum>i<d. cw i * \<theta> ^ i)"
    using Subfield.power_basis_span[OF sfQ alg_theta wE]
    by (auto simp: d_def)
  have dpos: "d > 0"
    unfolding d_def by (rule Subfield.ext_degree_pos[OF sfQ alg_theta])
  have coords: "rational_power_basis_coordinates d \<theta> ca cb cw a b w"
    by unfold_locales (use ca cb cw in auto)
  show thesis
    using coords d_def dpos that by blast
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
  then show ?thesis
    using Alg.mult_closed algebraic_elements_def alg by auto
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
    have "K \<union> {c * a} \<subseteq> generate_field (K \<union> {a})"
      using cK by (auto intro: generate_field_base)
    then show "generate_field (K \<union> {c * a}) \<subseteq> generate_field (K \<union> {a})"
      by (rule generate_field_least[OF subfield_generate_field])
  next
    have cG: "c \<in> generate_field (K \<union> {c * a})"
      using cK by (auto intro: generate_field_base)
    have caG: "c * a \<in> generate_field (K \<union> {c * a})"
      by (auto intro: generate_field_base)
    have aG: "a \<in> generate_field (K \<union> {c * a})"
      using Subfield.divide_closed \<open>c \<noteq> 0\<close> cG caG by force
    have "a = inverse c * (c * a)"
      using cnz by (simp add: field_simps)
    also have "\<dots> \<in> generate_field (K \<union> {c * a})"
      using cG by blast
    finally have aG: "a \<in> generate_field (K \<union> {c * a})" .
    have "K \<union> {a} \<subseteq> generate_field (K \<union> {c * a})"
      using aG cK by (auto intro: generate_field_base)
    then show "generate_field (K \<union> {a}) \<subseteq> generate_field (K \<union> {c * a})"
      by (rule generate_field_least[OF subfield_generate_field])
  qed
  have "eval_img K (c * a) = generate_field (K \<union> {c * a})"
    by (rule eval_img_eq_generate_field[OF alg_ca])
  also have "\<dots> = eval_img K a"
    using alg eval_img_eq_generate_field gen_eq by blast
  finally show ?thesis .
qed

lemma ext_degree_eq_of_eval_img_eq:
  assumes alg_a: "algebraic_over K a"
    and "algebraic_over K b" "eval_img K a = eval_img K b"
  shows "ext_degree K a = ext_degree K b"
proof -
  interpret T: finite_subfield_tower K "eval_img K a"
    by (rule finite_subfield_tower_simple[OF Subfield_axioms alg_a])
  show ?thesis
    using T.extension_degree_eq_ext_degree assms by metis
qed

lemma ext_degree_scale_eq:
  assumes "algebraic_over K a" "c \<in> K" "c \<noteq> 0"
  shows "ext_degree K (c * a) = ext_degree K a"
  by (simp add: algebraic_over_mult_of_in_field assms eval_img_scale_eq
      ext_degree_eq_of_eval_img_eq)

end

end
