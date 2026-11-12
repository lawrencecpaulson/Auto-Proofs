(*  Title:      Gelfond_Schneider/GS_Auxiliary.thy
    Author:     OpenAI Codex

Generic auxiliary-function infrastructure for Gelfond-Schneider. 
This packages (1) finite exponential sums; (2) the derivative
identities and (3) the distinct-exponent nonvanishing criterion.
*)

theory GS_Auxiliary
  imports GS_Algebraic
begin

section \<open>Finite Exponential Sums\<close>

definition gs_grid :: "nat \<Rightarrow> (nat \<times> nat) set"
  where "gs_grid q \<equiv> {..<q} \<times> {..<q}"

context gs_normalized_data
begin

definition gs_aux_fun :: "nat \<Rightarrow> ((nat \<times> nat) \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex"
  where
    "gs_aux_fun q \<eta> x \<equiv>
      (\<Sum>ab\<in>gs_grid q. \<eta> ab * exp (gs_rho (Suc (fst ab)) (Suc (snd ab)) * x))"

end

lemma has_field_derivative_exp_linear_right:
  "((\<lambda>x::complex. exp (x * z)) has_field_derivative z * exp (x * z)) (at x)"
  by (rule derivative_eq_intros | simp)+

lemma deriv_const_exp_linear_right:
  "deriv (\<lambda>x::complex. c * exp (x * z)) x = c * z * exp (x * z)"
  by (simp add: DERIV_cmult DERIV_imp_deriv mult.assoc
      has_field_derivative_exp_linear_right)

lemma iterated_deriv_exp_sum:
  assumes fin: "finite S"
  shows "((deriv ^^ k) (\<lambda>x::complex. \<Sum>i\<in>S. c i * exp (\<rho> i * x))) x =
         (\<Sum>i\<in>S. c i * \<rho> i ^ k * exp (\<rho> i * x))"
proof (induction k arbitrary: x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have "((deriv ^^ Suc k) (\<lambda>x. \<Sum>i\<in>S. c i * exp (\<rho> i * x))) x =
      deriv (\<lambda>x. \<Sum>i\<in>S. c i * \<rho> i ^ k * exp (\<rho> i * x)) x"
    using Suc.IH fin unfolding kth_deriv_simps
    by presburger
  also have "\<dots> = (\<Sum>i\<in>S. deriv (\<lambda>x. c i * \<rho> i ^ k * exp (\<rho> i * x)) x)"
    using DERIV_cmult DERIV_cmult_Id DERIV_fun_exp field_differentiable_def
      by (intro deriv_sum) blast
  also have "\<dots> = (\<Sum>i\<in>S. c i * \<rho> i ^ Suc k * exp (\<rho> i * x))"
    using deriv_const_exp_linear_right [of "c _ * \<rho> _ ^ k"] 
    by (force simp add: algebra_simps intro!: sum.cong)
  finally show ?case .
qed

lemma finite_exp_sum_eq_zero_imp_coeff_zero:
  fixes \<rho> :: "'a \<Rightarrow> complex"
  assumes fin: "finite S"
  assumes inj: "inj_on \<rho> S"
  assumes zero: "\<forall>x::complex. (\<Sum>i\<in>S. c i * exp (\<rho> i * x)) = 0"
  shows "\<forall>i\<in>S. c i = 0"
  using fin inj zero
proof (induction S arbitrary: c rule: finite_induct)
  case empty
  then show ?case
    by simp
next
  case (insert a S)
  have injS: "inj_on \<rho> S"
    using insert.prems(1) by auto
  have neq_a: "\<And>i. i \<in> S \<Longrightarrow> \<rho> i - \<rho> a \<noteq> 0"
    using insert unfolding inj_on_def
    by (metis insertCI right_minus_eq)
  have zero': "\<forall>x::complex. (\<Sum>i\<in>S. c i * (\<rho> i - \<rho> a) * exp (\<rho> i * x)) = 0"
  proof
    fix x
    have "deriv (\<lambda>x. \<Sum>i\<in>insert a S. c i * exp (\<rho> i * x)) x =
          (\<Sum>i\<in>insert a S. deriv (\<lambda>x. c i * exp (\<rho> i * x)) x)"
      by (intro deriv_sum) (metis DERIV_chain2 DERIV_cmult_Id DERIV_exp field_differentiable_def)
    also have "\<dots> = (\<Sum>i\<in>insert a S. c i * \<rho> i * exp (\<rho> i * x))"
      by (simp add: deriv_const_exp_linear_right mult.commute)
    finally have hder:
      "deriv (\<lambda>x. \<Sum>i\<in>insert a S. c i * exp (\<rho> i * x)) x =
        (\<Sum>i\<in>insert a S. c i * \<rho> i * exp (\<rho> i * x))" .
    have sum_rho0: "(\<Sum>i\<in>insert a S. c i * \<rho> i * exp (\<rho> i * x)) = 0"
      using insert.prems hder by auto
    have hcomb:
      "(\<Sum>i\<in>S. c i * (\<rho> i - \<rho> a) * exp (\<rho> i * x)) =
        (\<Sum>i\<in>insert a S. c i * \<rho> i * exp (\<rho> i * x)) -
        \<rho> a * (\<Sum>i\<in>insert a S. c i * exp (\<rho> i * x))"
      using insert.hyps by (simp add: algebra_simps sum_subtractf sum_distrib_left)
    show "(\<Sum>i\<in>S. c i * (\<rho> i - \<rho> a) * exp (\<rho> i * x)) = 0"
      unfolding hcomb using sum_rho0 insert.prems by simp
  qed
  have c_zero_S: "\<forall>i\<in>S. c i = 0"
    using insert.IH[OF injS zero'] neq_a by auto
  have h0: "(\<Sum>i\<in>insert a S. c i * exp (\<rho> i * 0)) = 0"
    using local.insert by blast
  with c_zero_S show ?case
    using insert.hyps by simp
qed

corollary finite_exp_sum_nonzero:
  fixes \<rho> :: "'a \<Rightarrow> complex"
  assumes fin: "finite S"
  assumes inj: "inj_on \<rho> S"
  assumes nz: "\<exists>i\<in>S. c i \<noteq> 0"
  shows "(\<lambda>x::complex. \<Sum>i\<in>S. c i * exp (\<rho> i * x)) \<noteq> (\<lambda>_. 0)"
  using finite_exp_sum_eq_zero_imp_coeff_zero[OF fin inj]
  using nz by meson

section \<open>Specialization to the Gelfond-Schneider Grid\<close>

context gs_normalized_data
begin

lemma gelfond_schneider_data_rho_inj_on_grid:
  shows "inj_on (\<lambda>ab. gs_rho (Suc (fst ab)) (Suc (snd ab))) (gs_grid q)"
  using gelfond_schneider_data_rho_injective
  by (meson inj_onI nat.inject prod.expand)

lemma gelfond_schneider_data_aux_fun_iterated_deriv:
  "((deriv ^^ k) (gs_aux_fun q \<eta>)) x =
    (\<Sum>ab\<in>gs_grid q.
      \<eta> ab *
      gs_rho (Suc (fst ab)) (Suc (snd ab)) ^ k *
      exp (gs_rho (Suc (fst ab)) (Suc (snd ab)) * x))"
  unfolding gs_aux_fun_def
  by (rule iterated_deriv_exp_sum) (simp add: gs_grid_def)

lemma gelfond_schneider_data_aux_fun_eq_zero_imp_coeff_zero:
  assumes zero: "gs_aux_fun q \<eta> = (\<lambda>_. 0)"
  shows "\<forall>ab\<in>gs_grid q. \<eta> ab = 0"
  unfolding gs_aux_fun_def
proof (rule finite_exp_sum_eq_zero_imp_coeff_zero)
  show "finite (gs_grid q)"
    by (simp add: gs_grid_def)
  show "inj_on (\<lambda>ab. gs_rho (Suc (fst ab)) (Suc (snd ab))) (gs_grid q)"
    by (rule gelfond_schneider_data_rho_inj_on_grid)
  show "\<forall>x. (\<Sum>i\<in>gs_grid q.
      \<eta> i * exp (gs_rho (Suc (fst i)) (Suc (snd i)) * x)) = 0"
    using assms gs_aux_fun_def by metis
qed

lemma gelfond_schneider_data_aux_fun_nonzero:
  assumes nz: "\<exists>ab\<in>gs_grid q. \<eta> ab \<noteq> 0"
  shows "gs_aux_fun q \<eta> \<noteq> (\<lambda>_. 0)"
  unfolding gs_aux_fun_def
proof (rule finite_exp_sum_nonzero)
  show "finite (gs_grid q)"
    by (simp add: gs_grid_def)
  show "inj_on (\<lambda>ab. gs_rho (Suc (fst ab)) (Suc (snd ab))) (gs_grid q)"
    by (rule gelfond_schneider_data_rho_inj_on_grid)
  show "\<exists>i\<in>gs_grid q. \<eta> i \<noteq> 0"
    using nz .
qed

end

end
