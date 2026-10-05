(*  Title:      Baker/Gelfond_Schneider_Power_Basis.thy
    Author:     OpenAI Codex

Qualitative power-basis infrastructure for the standalone Gelfond-Schneider
route.  This packages the primitive normal field, its indexed Galois family,
and the resulting monogenic basis values `emb i eta ^ j` at the level needed
before any quantitative inverse-Vandermonde bounds are introduced.
*)

theory Gelfond_Schneider_Power_Basis
  imports Gelfond_Schneider_Galois_Root_Bounds
begin

locale finite_galois_power_basis =
  fixes K :: "complex set"
  fixes eta :: complex
  fixes D :: nat
  fixes emb :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes K_def: "K = eval_img (\<rat> :: complex set) eta"
    and D_def: "D = ext_degree (\<rat> :: complex set) eta"
    and algQ: "algebraic_over (\<rat> :: complex set) eta"
    and eta_int: "algebraic_int eta"
    and ebij: "bij_betw emb {0..<D} (field_auto K (\<rat> :: complex set))"
begin

definition basis :: "nat \<Rightarrow> (complex \<Rightarrow> complex) \<Rightarrow> complex"
  where "basis j e = e eta ^ j"

lemma emb_in_field_auto:
  assumes "i < D"
  shows "emb i \<in> field_auto K (\<rat> :: complex set)"
  using ebij assms by (auto simp: bij_betw_def)

lemma indexed_images_inj:
  shows "inj_on (\<lambda>i. emb i eta) {0..<D}"
  by (rule indexed_galois_images_of_primitive_generator_inj[OF K_def algQ ebij])

lemma basis_indep_at_emb:
  assumes ilt: "i < D"
  assumes zero: "(\<Sum>j<D. of_int (c j) * basis j (emb i)) = 0"
  shows "\<forall>j<D. c j = 0"
proof -
  have "(\<Sum>j<D. of_int (c j) * (emb i eta) ^ j) = 0"
    using zero by (simp add: basis_def)
  then show ?thesis
    by (rule indexed_galois_image_power_basis_indep[OF K_def D_def algQ ebij ilt])
qed

lemma basis_algebraic_int_at_emb:
  assumes "i < D"
  shows "algebraic_int (basis j (emb i))"
  using indexed_galois_image_power_basis_algebraic_int[OF K_def D_def algQ ebij assms eta_int, of j]
  by (simp add: basis_def)

end

end
