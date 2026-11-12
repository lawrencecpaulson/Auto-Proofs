theory Statement_Audit
  imports Complex_Main
begin

text \<open>Green, Section 1 ("Introduction"), states the weighted prime
  bound and refers to an external argument for the zero-free consequence.
  This theory checks only an arithmetic deduction at the fixed even parameter
  C = 64, conditional on Green's bound and the external zero-sensitive
  Dirichlet-L estimate. The latter is outside the required project scope.\<close>

lemma fixed_scale_zero_gap:
  fixes L delta Sminus Splus Szero Sall :: real
  assumes large: "54 \<le> L"
    and partition: "Sall = Sminus + Splus + Szero"
    and mertens: "64 * L - 2 \<le> Sall"
    and green: "Sminus \<le> 43 * L + 517"
    and bias: "Splus + Szero / 2 \<le> 5 / 4 * L + 4096 * (delta * L) * L"
    and ramified: "Szero \<le> L"
  shows "77 / 32768 \<le> delta * L"
proof -
  have Lpos: "0 < L" using large by linarith
  have gap: "77 / 4 * L \<le> 519 + 4096 * (delta * L) * L"
    using partition mertens green bias ramified by linarith
  have err: "519 \<le> 77 / 8 * L" using large by linarith
  have main: "77 / 8 * L \<le> (4096 * (delta * L)) * L"
    using gap err by linarith
  have "77 / 8 \<le> 4096 * (delta * L)"
    using main Lpos by (simp add: mult_le_cancel_right_pos)
  then show ?thesis by linarith
qed

end
