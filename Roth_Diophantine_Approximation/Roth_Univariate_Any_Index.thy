theory Roth_Univariate_Any_Index
  imports Roth_Index_Dimension
begin

section \<open>One-variable index at an arbitrary coordinate\<close>

lemma roth_univariate_index_order_at:
  fixes p :: "rat poly" and r :: "nat \<Rightarrow> nat"
  assumes p: "p \<noteq> 0" and vm: "v<m" and rp: "r v > 0"
  shows "roth_index m r a (poly_to_mpoly v p) =
    ereal (real (Polynomial.order (a v) p) / real (r v))"
proof -
  let ?s = "pcompose p [:a v,1:]"
  let ?l = "Polynomial.order (a v) p"
  have snz: "?s \<noteq> 0"
    using p by (simp add: pcompose_eq_0_iff)
  have ord: "Polynomial.order 0 ?s = ?l"
    using roth_order_shift[OF p, of "a v"] .
  have low: "\<forall>k<?l. Polynomial.coeff ?s k = 0"
    and high: "Polynomial.coeff ?s ?l \<noteq> 0"
    using roth_order_zero_coeff[OF snz] ord by auto
  have tcl: "roth_taylor_coeff a
      (Poly_Mapping.single v ?l) (poly_to_mpoly v p) \<noteq> 0"
    using high by (simp add: roth_univariate_taylor_coeff)
  have w: "roth_weight m r (Poly_Mapping.single v ?l) =
    real ?l / real (r v)"
    by (rule roth_weight_single[OF vm])
  have ub: "roth_index m r a (poly_to_mpoly v p) \<le>
    ereal (real ?l / real (r v))"
    using roth_index_le_coeff[OF tcl, of m r] w by metis
  have pmp: "poly_to_mpoly v p \<noteq> 0"
    by (rule roth_poly_to_mpoly_nonzero[OF p])
  obtain I where tc: "roth_taylor_coeff a I (poly_to_mpoly v p) \<noteq> 0"
    and ieq: "roth_index m r a (poly_to_mpoly v p) =
      ereal (roth_weight m r I)"
    using roth_index_attained[OF pmp, where m=m and r=r and a=a]
    by blast
  have irep: "I = Poly_Mapping.single v (Poly_Mapping.lookup I v)"
    by (rule roth_univariate_taylor_support[OF tc])
  have kcoeff: "Polynomial.coeff ?s (Poly_Mapping.lookup I v) \<noteq> 0"
    using tc irep roth_univariate_taylor_coeff by metis
  have lk: "?l \<le> Poly_Mapping.lookup I v"
    using low kcoeff by (metis not_le_imp_less)
  have wI: "roth_weight m r I =
    real (Poly_Mapping.lookup I v) / real (r v)"
  proof -
    have "roth_weight m r I =
      roth_weight m r
        (Poly_Mapping.single v (Poly_Mapping.lookup I v))"
      by (rule arg_cong[OF irep])
    also have "... = real (Poly_Mapping.lookup I v) / real (r v)"
      by (rule roth_weight_single[OF vm])
    finally show ?thesis .
  qed
  have lb: "ereal (real ?l / real (r v)) \<le>
      roth_index m r a (poly_to_mpoly v p)"
    using ieq wI lk rp by (simp add: divide_right_mono)
  show ?thesis by (rule antisym[OF ub lb])
qed

lemma roth_univariate_index_bound_at:
  fixes P :: "rat mpoly" and r :: "nat \<Rightarrow> nat"
  assumes P: "P \<noteq> 0" and pv: "vars P \<subseteq> {v}"
    and vm: "v<m" and rp: "r v > 0"
    and deg: "degree (mpoly_to_poly v P) \<le> r v"
    and eta: "eta > 0"
    and h: "roth_proj_log_height P + real (r v) \<le>
      eta * real (r v) * roth_rat_log_height (a v)"
  shows "roth_index m r a P \<le> ereal eta"
proof -
  let ?p = "mpoly_to_poly v P"
  have pn: "?p \<noteq> 0"
    by (rule roth_mpoly_to_poly_nonzero[OF P pv])
  have peq: "poly_to_mpoly v ?p = P"
    by (rule mpoly_to_poly_inverse[OF pv])
  have rpos: "(0::real) < real (r v)" using rp by simp
  have posprod: "0 < eta * real (r v) * roth_rat_log_height (a v)"
    using h rpos roth_proj_log_height_nonneg[of P] by linarith
  have ep: "0 < eta * real (r v)" using eta rpos by simp
  have hp: "0 < roth_rat_log_height (a v)"
    using posprod ep by (auto simp: zero_less_mult_iff)
  have b: "real (Polynomial.order (a v) ?p) *
      roth_rat_log_height (a v) \<le>
    roth_proj_log_height P + real (degree ?p)"
    by (rule roth_univariate_mpoly_log_order_bound[OF P pv])
  have bd: "real (Polynomial.order (a v) ?p) *
      roth_rat_log_height (a v) \<le>
    eta * real (r v) * roth_rat_log_height (a v)"
    using b deg h by linarith
  have l: "real (Polynomial.order (a v) ?p) \<le> eta * real (r v)"
    using bd hp by (simp add: mult_le_cancel_right_pos)
  have ratio: "real (Polynomial.order (a v) ?p) / real (r v) \<le> eta"
    using l rpos by (simp add: pos_divide_le_eq)
  have io: "roth_index m r a (poly_to_mpoly v ?p) =
    ereal (real (Polynomial.order (a v) ?p) / real (r v))"
    by (rule roth_univariate_index_order_at)
      (use pn vm rp in auto)
  show ?thesis using io peq ratio by simp
qed


lemma roth_univariate_degree_of_box_at:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box (Suc n) r P"
  shows "degree (mpoly_to_poly n P) \<le> r n"
proof (rule degree_le, intro allI impI)
  fix i assume i: "r n < i"
  have outside: "Poly_Mapping.single n i \<notin>
      roth_exponent_box (Suc n) r"
    using i by (auto simp: roth_exponent_box_iff)
  show "Polynomial.coeff (mpoly_to_poly n P) i = 0"
    using roth_coeff_zero_outside_box[OF box outside] by simp
qed


lemma roth_univariate_index_bound_degree_at:
  fixes P :: "rat mpoly" and r :: "nat \<Rightarrow> nat"
  assumes P: "P \<noteq> 0" and pv: "vars P \<subseteq> {v}"
    and vm: "v<m" and rp: "r v > 0" and Dp: "D > 0"
    and deg: "degree (mpoly_to_poly v P) \<le> D"
    and eta: "eta > 0"
    and h: "roth_proj_log_height P + real D \<le>
      eta * real D * roth_rat_log_height (a v)"
  shows "roth_index m r a P \<le>
    ereal (eta * real D / real (r v))"
proof -
  let ?p = "mpoly_to_poly v P"
  have pn: "?p \<noteq> 0"
    by (rule roth_mpoly_to_poly_nonzero[OF P pv])
  have peq: "poly_to_mpoly v ?p = P"
    by (rule mpoly_to_poly_inverse[OF pv])
  have rpos: "(0::real) < real (r v)" using rp by simp
  have posprod: "0 < eta * real D * roth_rat_log_height (a v)"
    using h Dp roth_proj_log_height_nonneg[of P] by linarith
  have ep: "0 < eta * real D" using eta Dp by simp
  have hp: "0 < roth_rat_log_height (a v)"
    using posprod ep by (auto simp: zero_less_mult_iff)
  have b: "real (Polynomial.order (a v) ?p) *
      roth_rat_log_height (a v) \<le>
    roth_proj_log_height P + real (degree ?p)"
    by (rule roth_univariate_mpoly_log_order_bound[OF P pv])
  have bd: "real (Polynomial.order (a v) ?p) *
      roth_rat_log_height (a v) \<le>
    eta * real D * roth_rat_log_height (a v)"
    using b deg h by linarith
  have l: "real (Polynomial.order (a v) ?p) \<le> eta * real D"
    using bd hp by (simp add: mult_le_cancel_right_pos)
  have ratio: "real (Polynomial.order (a v) ?p) / real (r v) \<le>
      eta * real D / real (r v)"
    using l rpos by (simp add: divide_right_mono)
  have io: "roth_index m r a (poly_to_mpoly v ?p) =
    ereal (real (Polynomial.order (a v) ?p) / real (r v))"
    by (rule roth_univariate_index_order_at)
      (use pn vm rp in auto)
  show ?thesis using io peq ratio by simp
qed

end
