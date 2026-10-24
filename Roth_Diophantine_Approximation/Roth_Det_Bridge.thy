theory Roth_Det_Bridge
  imports Roth_Determinant_Index
begin

theorem roth_det_bounds_bridge:
  fixes P :: "rat mpoly"
  assumes box: "roth_poly_in_box (Suc (Suc n)) r P"
    and nz: "P \<noteq> 0"
    and half: "\<And>v. Suc v < Suc (Suc n) \<Longrightarrow>
      2 * r (Suc v) \<le> r v"
    and rp: "0 < r n" and rl: "0 < r (Suc n)"
  shows "\<exists>k mu V. 0 < k \<and> k \<le> Suc (r (Suc n)) \<and>
    V = det (mat k k (\<lambda>(i,j).
      roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P)) \<and>
    V \<noteq> 0 \<and>
    roth_proj_log_height V \<le>
      real k * (roth_proj_log_height P + 4 * real (r 0)) \<and>
    ereal (real k *
      (real_of_ereal (roth_index (Suc (Suc n)) r a P))^2 /
        (2 * real (Suc (Suc n)))) \<le>
      roth_index (Suc (Suc n)) r a V +
        ereal (real k * (real (r (Suc n)) / real (r n)))"
proof -
  obtain k mu where kp: "0<k" and kn: "k \<le> Suc (r (Suc n))"
    and row: "\<forall>i<k. Poly_Mapping.keys (mu i) \<subseteq> {..<Suc n} \<and>
      roth_total_order (Suc n) (mu i) \<le> i"
    and vn: "det (mat k k (\<lambda>(i,j).
      roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P)) \<noteq> 0"
    using roth_box_tensor_det_nonzero[OF box nz] by blast
  let ?V = "det (mat k k (\<lambda>(i,j).
    roth_hasse (mu i + Poly_Mapping.single (Suc n) j) P))"
  have hb: "roth_proj_log_height ?V \<le>
    real k * (roth_proj_log_height P + 4 * real (r 0))"
    by (rule roth_hasse_det_log_bound_sharp[OF box nz half])
      (use kn in auto)
  have ib: "ereal (real k *
      (real_of_ereal (roth_index (Suc (Suc n)) r a P))^2 /
        (2 * real (Suc (Suc n)))) \<le>
      roth_index (Suc (Suc n)) r a ?V +
        ereal (real k * (real (r (Suc n)) / real (r n)))"
    by (rule roth_tensor_det_index_quadratic_box[OF box nz half rp rl kn])
      (use row in auto)
  show ?thesis using kp kn vn hb ib by blast
qed

end
