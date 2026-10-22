theory Stokes_Halfline_Forms
  imports Stokes_Local
begin

text \<open>
  In dimension one a near-top form is a scalar function.  Its
  exterior derivative is the ordinary derivative.  The boundary is
  zero-dimensional, so its integral is evaluation at the endpoint
  with outward-normal-first sign.
\<close>

definition halfline_exterior_one :: "(real \<Rightarrow> real) \<Rightarrow>
    real \<Rightarrow> real"
  where "halfline_exterior_one F t = vector_derivative F (at t)"

definition halfline_boundary_coeff :: "(real \<Rightarrow> real) \<Rightarrow>
    real"
  where "halfline_boundary_coeff F = - F 0"

definition finite_boundary_zero_integral ::
    "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real"
  where "finite_boundary_zero_integral B a =
    (\<Sum>p\<in>B. a p)"

lemma halfline_boundary_as_zero_integral:
  "halfline_boundary_coeff F =
    finite_boundary_zero_integral {0::real}
      (\<lambda>t. - F t)"
  by (simp add: halfline_boundary_coeff_def
    finite_boundary_zero_integral_def)

theorem Stokes_halfline_form_C1:
  fixes F :: "real \<Rightarrow> real"
  assumes deriv: "\<And>t. 0 \<le> t \<Longrightarrow>
      F differentiable (at t)"
    and cont: "continuous_on {0..} (halfline_exterior_one F)"
    and support: "compact (closure
      {t. 0 \<le> t \<and> F t \<noteq> 0})"
  shows "(LINT t : {0..} | lborel. halfline_exterior_one F t) =
    halfline_boundary_coeff F"
proof -
  have d: "\<And>t. 0 \<le> t \<Longrightarrow>
      (F has_vector_derivative halfline_exterior_one F t) (at t)"
    using deriv
    by (simp add: halfline_exterior_one_def vector_derivative_works)
  have "(LINT t : {0..} | lborel. halfline_exterior_one F t) =
      - F 0"
    by (rule halfline_FTC_compact_support[OF d cont support])
  then show ?thesis
    by (simp add: halfline_boundary_coeff_def)
qed

corollary Stokes_halfline_form_C1_zero_integral:
  fixes F :: "real \<Rightarrow> real"
  assumes deriv: "\<And>t. 0 \<le> t \<Longrightarrow>
      F differentiable (at t)"
    and cont: "continuous_on {0..} (halfline_exterior_one F)"
    and support: "compact (closure
      {t. 0 \<le> t \<and> F t \<noteq> 0})"
  shows "(LINT t : {0..} | lborel.
      halfline_exterior_one F t) =
    finite_boundary_zero_integral {0::real}
      (\<lambda>t. - F t)"
  using Stokes_halfline_form_C1[OF deriv cont support]
  by (simp add: halfline_boundary_as_zero_integral)

end
