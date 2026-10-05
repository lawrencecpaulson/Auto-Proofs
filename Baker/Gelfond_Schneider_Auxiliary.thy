(*  Title:      Baker/Gelfond_Schneider_Auxiliary.thy
    Author:     OpenAI Codex

Generic auxiliary-function infrastructure for the standalone
Gelfond-Schneider port. This packages the finite exponential sums that later
play the role of Lean's auxiliary function `R`, together with the derivative
identities and the distinct-exponent nonvanishing criterion needed in the
`MainOrder` part of the argument.
*)

theory Gelfond_Schneider_Auxiliary
  imports Gelfond_Schneider_Algebraic
begin

declare [[apply_timeout = 10]]

section \<open>Finite Exponential Sums\<close>

definition gs_grid :: "nat \<Rightarrow> (nat \<times> nat) set"
  where "gs_grid q = {..<q} \<times> {..<q}"

definition gs_aux_fun ::
  "gelfond_schneider_data \<Rightarrow> nat \<Rightarrow> ((nat \<times> nat) \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex"
  where
    "gs_aux_fun d q \<eta> x =
      (\<Sum>ab\<in>gs_grid q. \<eta> ab * exp (gs_rho d (Suc (fst ab)) (Suc (snd ab)) * x))"

lemma has_field_derivative_exp_linear_right:
  "((\<lambda>x::complex. exp (x * z)) has_field_derivative z * exp (x * z)) (at x)"
proof -
  have "((\<lambda>x::complex. exp (x * z)) has_field_derivative exp (x * z) * z) (at x)"
  proof -
    have gderiv: "((\<lambda>x::complex. x * z) has_field_derivative 1 * z) (at x within UNIV)"
      by (rule DERIV_cmult_right[OF DERIV_ident])
    have "((\<lambda>x::complex. exp (x * z)) has_field_derivative exp (x * z) * (1 * z))
        (at x within UNIV)"
      by (rule DERIV_chain2[OF DERIV_exp gderiv])
    then show ?thesis
      by simp
  qed
  then show ?thesis
    by (rule DERIV_cong) (simp add: algebra_simps)
qed

lemma has_field_derivative_exp_linear:
  "((\<lambda>x::complex. exp (z * x)) has_field_derivative z * exp (z * x)) (at x)"
proof -
  have eq_fun: "(\<lambda>x::complex. exp (z * x)) = (\<lambda>x. exp (x * z))"
    by (simp add: fun_eq_iff mult.commute)
  have "((\<lambda>x::complex. exp (z * x)) has_field_derivative z * exp (x * z)) (at x)"
    by (simp only: eq_fun has_field_derivative_exp_linear_right)
  then show ?thesis
    by (rule DERIV_cong) (simp add: mult.commute)
qed

lemma deriv_const_exp_linear_right:
  "deriv (\<lambda>x::complex. c * exp (x * z)) x = c * z * exp (x * z)"
proof -
  have "((\<lambda>x::complex. c * exp (x * z)) has_field_derivative c * (z * exp (x * z))) (at x)"
    by (rule DERIV_cmult[OF has_field_derivative_exp_linear_right])
  then show ?thesis
    by (simp add: has_field_derivative_def DERIV_imp_deriv)
qed

lemma deriv_const_exp_linear:
  "deriv (\<lambda>x::complex. c * exp (z * x)) x = c * z * exp (z * x)"
proof -
  have eq_fun: "(\<lambda>x::complex. c * exp (z * x)) = (\<lambda>x. c * exp (x * z))"
    by (simp add: fun_eq_iff mult.commute)
  have "deriv (\<lambda>x::complex. c * exp (z * x)) x = deriv (\<lambda>x. c * exp (x * z)) x"
    by (simp only: eq_fun)
  also have "\<dots> = c * z * exp (x * z)"
    by (rule deriv_const_exp_linear_right)
  finally show ?thesis
    by (simp add: mult.commute)
qed

lemma iterated_deriv_const_exp_linear:
  "((deriv ^^ k) (\<lambda>x::complex. c * exp (z * x))) x = c * z ^ k * exp (z * x)"
proof (induction k arbitrary: x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have fun_eq: "(deriv ^^ k) (\<lambda>x. c * exp (z * x)) = (\<lambda>x. c * z ^ k * exp (z * x))"
    by (rule ext) (simp add: Suc.IH)
  have "((deriv ^^ Suc k) (\<lambda>x. c * exp (z * x))) x =
      deriv (\<lambda>x. c * z ^ k * exp (z * x)) x"
    by (simp add: fun_eq)
  also have "\<dots> = c * z ^ Suc k * exp (z * x)"
  proof -
    have "deriv (\<lambda>x. c * z ^ k * exp (z * x)) x =
        (c * z ^ k) * z * exp (z * x)"
      by (rule deriv_const_exp_linear)
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  finally show ?case .
qed

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
  have fun_eq: "(deriv ^^ k) (\<lambda>x. \<Sum>i\<in>S. c i * exp (\<rho> i * x)) =
      (\<lambda>x. \<Sum>i\<in>S. c i * \<rho> i ^ k * exp (\<rho> i * x))"
    by (rule ext) (simp add: Suc.IH fin)
  have "((deriv ^^ Suc k) (\<lambda>x. \<Sum>i\<in>S. c i * exp (\<rho> i * x))) x =
      deriv (\<lambda>x. \<Sum>i\<in>S. c i * \<rho> i ^ k * exp (\<rho> i * x)) x"
    by (simp add: fun_eq)
  also have "\<dots> = (\<Sum>i\<in>S. deriv (\<lambda>x. c i * \<rho> i ^ k * exp (\<rho> i * x)) x)"
  proof (rule deriv_sum)
    fix i
    show "(\<lambda>x. c i * \<rho> i ^ k * exp (\<rho> i * x)) field_differentiable at x"
    proof -
      have eq_fun: "(\<lambda>x. c i * \<rho> i ^ k * exp (\<rho> i * x)) =
          (\<lambda>x. (c i * \<rho> i ^ k) * exp (x * \<rho> i))"
        by (simp add: fun_eq_iff algebra_simps mult.commute)
      have "((\<lambda>x. (c i * \<rho> i ^ k) * exp (x * \<rho> i)) has_field_derivative
          (c i * \<rho> i ^ k) * (\<rho> i * exp (x * \<rho> i))) (at x)"
        by (rule DERIV_cmult[OF has_field_derivative_exp_linear_right])
      then have "(\<lambda>x. (c i * \<rho> i ^ k) * exp (x * \<rho> i)) field_differentiable at x"
        unfolding field_differentiable_def by blast
      then show ?thesis
        by (simp only: eq_fun)
    qed
  qed
  also have "\<dots> = (\<Sum>i\<in>S. c i * \<rho> i ^ Suc k * exp (\<rho> i * x))"
  proof (rule sum.cong[OF refl])
    fix i
    assume "i \<in> S"
    have "deriv (\<lambda>xa. c i * \<rho> i ^ k * exp (xa * \<rho> i)) x =
        (c i * \<rho> i ^ k) * \<rho> i * exp (x * \<rho> i)"
      by (rule deriv_const_exp_linear_right)
    then show "deriv (\<lambda>x. c i * \<rho> i ^ k * exp (\<rho> i * x)) x =
        c i * \<rho> i ^ Suc k * exp (\<rho> i * x)"
      by (simp add: algebra_simps mult.commute)
  qed
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
  proof -
    fix i
    assume iS: "i \<in> S"
    have "\<rho> i \<noteq> \<rho> a"
    proof
      assume "\<rho> i = \<rho> a"
      then have "i = a"
        using insert.prems(1) iS insert.hyps
        unfolding inj_on_def by blast
      with iS insert.hyps show False
        by simp
    qed
    then show "\<rho> i - \<rho> a \<noteq> 0"
      by simp
  qed
  have zero': "\<forall>x::complex. (\<Sum>i\<in>S. c i * (\<rho> i - \<rho> a) * exp (\<rho> i * x)) = 0"
  proof
    fix x :: complex
    have hfun0: "(\<Sum>i\<in>insert a S. c i * exp (\<rho> i * x)) = 0"
      using insert.prems(2) by simp
    have hder0: "deriv (\<lambda>x. \<Sum>i\<in>insert a S. c i * exp (\<rho> i * x)) x = 0"
      using insert.prems(2) by simp
    have hder:
      "deriv (\<lambda>x. \<Sum>i\<in>insert a S. c i * exp (\<rho> i * x)) x =
        (\<Sum>i\<in>insert a S. c i * \<rho> i * exp (\<rho> i * x))"
    proof -
      have "deriv (\<lambda>x. \<Sum>i\<in>insert a S. c i * exp (\<rho> i * x)) x =
          (\<Sum>i\<in>insert a S. deriv (\<lambda>x. c i * exp (\<rho> i * x)) x)"
      proof (rule deriv_sum)
        fix i
        show "(\<lambda>x. c i * exp (\<rho> i * x)) field_differentiable at x"
        proof -
          have eq_fun: "(\<lambda>x. c i * exp (\<rho> i * x)) = (\<lambda>x. c i * exp (x * \<rho> i))"
            by (simp add: fun_eq_iff mult.commute)
          have "((\<lambda>x. c i * exp (x * \<rho> i)) has_field_derivative
              c i * (\<rho> i * exp (x * \<rho> i))) (at x)"
            by (rule DERIV_cmult[OF has_field_derivative_exp_linear_right])
          then have "(\<lambda>x. c i * exp (x * \<rho> i)) field_differentiable at x"
            unfolding field_differentiable_def by blast
          then show ?thesis
            by (simp only: eq_fun)
        qed
      qed
      also have "\<dots> = (\<Sum>i\<in>insert a S. c i * \<rho> i * exp (\<rho> i * x))"
      proof (rule sum.cong[OF refl])
        fix i
        assume "i \<in> insert a S"
        have "deriv (\<lambda>xa. c i * exp (xa * \<rho> i)) x =
            c i * \<rho> i * exp (x * \<rho> i)"
          by (rule deriv_const_exp_linear_right)
        then show "deriv (\<lambda>x. c i * exp (\<rho> i * x)) x =
            c i * \<rho> i * exp (\<rho> i * x)"
          by (simp add: mult.commute)
      qed
      finally show ?thesis .
    qed
    have sum_rho0: "(\<Sum>i\<in>insert a S. c i * \<rho> i * exp (\<rho> i * x)) = 0"
      using hder0 hder by simp
    have hcomb:
      "(\<Sum>i\<in>S. c i * (\<rho> i - \<rho> a) * exp (\<rho> i * x)) =
        (\<Sum>i\<in>insert a S. c i * \<rho> i * exp (\<rho> i * x)) -
        \<rho> a * (\<Sum>i\<in>insert a S. c i * exp (\<rho> i * x))"
    proof -
      have sum_rho:
        "(\<Sum>i\<in>insert a S. c i * \<rho> i * exp (\<rho> i * x)) =
          c a * \<rho> a * exp (\<rho> a * x) + (\<Sum>i\<in>S. c i * \<rho> i * exp (\<rho> i * x))"
        using insert.hyps by simp
      have sum_exp:
        "(\<Sum>i\<in>insert a S. c i * exp (\<rho> i * x)) =
          c a * exp (\<rho> a * x) + (\<Sum>i\<in>S. c i * exp (\<rho> i * x))"
        using insert.hyps by simp
      show ?thesis
        unfolding sum_rho sum_exp
        by (simp add: algebra_simps sum_subtractf sum_distrib_left)
    qed
    show "(\<Sum>i\<in>S. c i * (\<rho> i - \<rho> a) * exp (\<rho> i * x)) = 0"
      unfolding hcomb using sum_rho0 hfun0 by simp
  qed
  have IH':
    "\<forall>i\<in>S. c i * (\<rho> i - \<rho> a) = 0"
    by (rule insert.IH[OF injS zero'])
  have c_zero_S: "\<forall>i\<in>S. c i = 0"
    using IH' neq_a by auto
  have h0: "(\<Sum>i\<in>insert a S. c i * exp (\<rho> i * 0)) = 0"
    using insert.prems(2)[rule_format, of 0] .
  have "c a = 0"
    using insert.hyps c_zero_S h0 by simp
  with c_zero_S show ?case
    using insert.hyps by simp
qed

corollary finite_exp_sum_nonzero:
  fixes \<rho> :: "'a \<Rightarrow> complex"
  assumes fin: "finite S"
  assumes inj: "inj_on \<rho> S"
  assumes nz: "\<exists>i\<in>S. c i \<noteq> 0"
  shows "(\<lambda>x::complex. \<Sum>i\<in>S. c i * exp (\<rho> i * x)) \<noteq> (\<lambda>_. 0)"
proof
  assume h0: "(\<lambda>x::complex. \<Sum>i\<in>S. c i * exp (\<rho> i * x)) = (\<lambda>_. 0)"
  have h0': "\<forall>x::complex. (\<Sum>i\<in>S. c i * exp (\<rho> i * x)) = 0"
    using h0 by (simp add: fun_eq_iff)
  have "\<forall>i\<in>S. c i = 0"
    by (rule finite_exp_sum_eq_zero_imp_coeff_zero[OF fin inj h0'])
  with nz show False
    by blast
qed

section \<open>Specialization to the Gelfond-Schneider Grid\<close>

lemma gelfond_schneider_data_rho_inj_on_grid:
  assumes d: "is_gelfond_schneider_data d"
  shows "inj_on (\<lambda>ab. gs_rho d (Suc (fst ab)) (Suc (snd ab))) (gs_grid q)"
proof (rule inj_onI)
  fix ab ab'
  assume ab: "ab \<in> gs_grid q"
  assume ab': "ab' \<in> gs_grid q"
  assume eq: "gs_rho d (Suc (fst ab)) (Suc (snd ab)) =
    gs_rho d (Suc (fst ab')) (Suc (snd ab'))"
  have "Suc (fst ab) = Suc (fst ab') \<and> Suc (snd ab) = Suc (snd ab')"
    by (rule gelfond_schneider_data_rho_injective[OF d eq])
  then show "ab = ab'"
    by (cases ab; cases ab'; simp)
qed

lemma gelfond_schneider_data_aux_fun_iterated_deriv:
  "((deriv ^^ k) (gs_aux_fun d q \<eta>)) x =
    (\<Sum>ab\<in>gs_grid q.
      \<eta> ab *
      gs_rho d (Suc (fst ab)) (Suc (snd ab)) ^ k *
      exp (gs_rho d (Suc (fst ab)) (Suc (snd ab)) * x))"
  unfolding gs_aux_fun_def
  by (rule iterated_deriv_exp_sum) (simp add: gs_grid_def)

lemma gelfond_schneider_data_aux_fun_eq_zero_imp_coeff_zero:
  assumes d: "is_gelfond_schneider_data d"
  assumes zero: "gs_aux_fun d q \<eta> = (\<lambda>_. 0)"
  shows "\<forall>ab\<in>gs_grid q. \<eta> ab = 0"
  unfolding gs_aux_fun_def
proof (rule finite_exp_sum_eq_zero_imp_coeff_zero)
  show "finite (gs_grid q)"
    by (simp add: gs_grid_def)
  show "inj_on (\<lambda>ab. gs_rho d (Suc (fst ab)) (Suc (snd ab))) (gs_grid q)"
    by (rule gelfond_schneider_data_rho_inj_on_grid[OF d])
  show "\<forall>x. (\<Sum>i\<in>gs_grid q.
      \<eta> i * exp (gs_rho d (Suc (fst i)) (Suc (snd i)) * x)) = 0"
  proof
    fix x
    have "(gs_aux_fun d q \<eta>) x = (\<lambda>_. 0) x"
      using fun_cong[OF zero, of x] .
    then show "(\<Sum>i\<in>gs_grid q.
        \<eta> i * exp (gs_rho d (Suc (fst i)) (Suc (snd i)) * x)) = 0"
      unfolding gs_aux_fun_def by simp
  qed
qed

lemma gelfond_schneider_data_aux_fun_nonzero:
  assumes d: "is_gelfond_schneider_data d"
  assumes nz: "\<exists>ab\<in>gs_grid q. \<eta> ab \<noteq> 0"
  shows "gs_aux_fun d q \<eta> \<noteq> (\<lambda>_. 0)"
  unfolding gs_aux_fun_def
proof (rule finite_exp_sum_nonzero)
  show "finite (gs_grid q)"
    by (simp add: gs_grid_def)
  show "inj_on (\<lambda>ab. gs_rho d (Suc (fst ab)) (Suc (snd ab))) (gs_grid q)"
    by (rule gelfond_schneider_data_rho_inj_on_grid[OF d])
  show "\<exists>i\<in>gs_grid q. \<eta> i \<noteq> 0"
    using nz .
qed

end
