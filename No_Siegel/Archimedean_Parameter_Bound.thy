theory Archimedean_Parameter_Bound
  imports Archimedean_Log_Bound
begin

text \<open>An explicit version of the last estimate in Green's Section 4.
  The constant 11 absorbs the three finite parameter errors.\<close>

lemma green_archimedean_parameter_coefficient:
  fixes c x j :: real
  assumes cge: "2 \<le> c" and xge: "c \<le> x"
    and jnonneg: "0 \<le> j" and jcap: "c * j \<le> x"
  shows "4 * c + 2 * j * c + (x + j) * (c + 5) / 2
    \<le> x * (c + 22) / 2"
proof -
  have jhalf: "2 * j \<le> x"
  proof -
    have "2 * j \<le> c * j"
      by (rule mult_right_mono[OF cge jnonneg])
    then show ?thesis using jcap by linarith
  qed
  have bound: "8 * c + 5 * (c * j) + 5 * j
      \<le> 8 * x + 5 * x + (5 / 2) * x"
    using xge jcap jhalf by linarith
  have identity:
    "x * (c + 22) / 2 -
      (4 * c + 2 * j * c + (x + j) * (c + 5) / 2) =
      (17 * x - 8 * c - 5 * (c * j) - 5 * j) / 2"
    by (simp add: field_simps; algebra)
  have "0 \<le> (17 * x - 8 * c - 5 * (c * j) - 5 * j) / 2"
    using bound xge cge by (simp add: field_simps; linarith)
  then show ?thesis using identity by linarith
qed

lemma green_archimedean_log_four:
  fixes q :: nat
  assumes qge: "2 \<le> q"
  shows "ln (4::real) \<le> 2 * ln (real q)"
proof -
  have sq: "(4::real) \<le> (real q)\<^sup>2"
  proof -
    have nat_bound: "(2::nat) * 2 \<le> q * q"
      by (rule mult_mono[OF qge qge]) simp_all
    have "real ((2::nat) * 2) \<le> real (q * q)"
      by (rule of_nat_mono[OF nat_bound])
    then show ?thesis by (simp add: power2_eq_square)
  qed
  have "ln (4::real) \<le> ln ((real q)\<^sup>2)"
    by (rule ln_mono) (use sq in simp_all)
  also have "... = 2 * ln (real q)"
    by (simp add: ln_realpow)
  finally show ?thesis .
qed

lemma green_archimedean_log_box:
  fixes q cparam :: nat
  assumes qge: "2 \<le> q" and even: "even cparam"
  shows "ln (2 * real (green_N q cparam) * sqrt (real q))
    \<le> (real cparam + 5) / 2 * ln (real q)"
proof -
  have qpos: "0 < real q" using qge by simp
  have sqrtpos: "0 < sqrt (real q)" using qpos by simp
  have Nlog: "ln (2 * real (green_N q cparam) * sqrt (real q)) =
      ln 4 + real (cparam div 2) * ln (real q) +
        ln (real q) / 2"
    using qpos sqrtpos
    by (simp add: green_N_def ln_mult ln_realpow ln_sqrt
      algebra_simps)
  have half: "real (cparam div 2) = real cparam / 2"
  proof -
    have "cparam = cparam div 2 + cparam div 2"
      using even_two_times_div_two[OF even] by (simp add: mult_2)
    then show ?thesis by simp
  qed
  have "ln (2 * real (green_N q cparam) * sqrt (real q))
      \<le> 2 * ln (real q) + real cparam / 2 * ln (real q) +
        ln (real q) / 2"
    using Nlog half green_archimedean_log_four[OF qge]
    by simp
  also have "... = (real cparam + 5) / 2 * ln (real q)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma green_archimedean_paper_first_log:
  fixes q cparam :: nat
  assumes even: "even cparam" and cge: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
  shows "ln (2 * real (green_N q cparam * green_N q cparam *
      green_J q cparam)) \<le> 4 * ln (real (green_X q cparam))"
proof -
  let ?t = "q ^ (cparam div 2)"
  let ?X = "green_X q cparam"
  let ?N = "green_N q cparam"
  let ?J = "green_J q cparam"
  have square: "?X = ?t * ?t"
    by (rule green_even_exponent_square[OF even])
  have tge: "4 \<le> ?t" using cge large by linarith
  have Xge: "16 \<le> real ?X"
  proof -
    have nat_bound: "4 * 4 \<le> ?t * ?t"
      by (rule mult_mono[OF tge tge]) simp_all
    have "real (4 * 4) \<le> real (?t * ?t)"
      by (rule of_nat_mono[OF nat_bound])
    then show ?thesis by (simp add: square)
  qed
  have Nsquare: "real (?N * ?N) = 4 * real ?X"
    by (simp add: green_N_def square algebra_simps)
  have Jle: "real ?J \<le> real ?X"
    by (simp add: green_J_def)
  have cap: "2 * real (?N * ?N * ?J) \<le> (real ?X) ^ 4"
  proof -
    have "2 * real (?N * ?N * ?J) =
        8 * real ?X * real ?J"
      using Nsquare by (simp add: algebra_simps)
    also have "... \<le> 8 * (real ?X)\<^sup>2"
    proof -
      have "real ?X * real ?J \<le> real ?X * real ?X"
        by (rule mult_left_mono[OF Jle]) (use Xge in simp)
      then show ?thesis by (simp add: power2_eq_square)
    qed
    also have "... \<le> (real ?X)^4"
    proof -
      have sqge: "8 \<le> (real ?X)\<^sup>2"
      proof -
        have "real ?X \<le> (real ?X)\<^sup>2"
          using Xge by (simp add: power2_eq_square; intro mult_right_mono;
            simp)
        then show ?thesis using Xge by linarith
      qed
      have "8 * (real ?X)\<^sup>2 \<le>
          (real ?X)\<^sup>2 * (real ?X)\<^sup>2"
        by (rule mult_right_mono[OF sqge]) simp
      then show ?thesis by (simp add: power_add)
    qed
    finally show ?thesis .
  qed
  have pos: "0 < (2 * real (?N * ?N * ?J))"
  proof -
    have tpos: "0 < ?t" using tge by linarith
    have Npos: "0 < ?N" using tpos by (simp add: green_N_def)
    have Jge: "?N \<le> ?J"
      by (rule green_paper_row_parameters(1)[OF even cge large])
    have "0 < ?J" using Npos Jge by linarith
    then show ?thesis using Npos by simp
  qed
  have "ln (2 * real (?N * ?N * ?J)) \<le> ln ((real ?X)^4)"
    by (rule ln_mono) (use pos cap in simp_all)
  also have "... = 4 * ln (real ?X)"
    by (simp add: ln_realpow)
  finally show ?thesis .
qed

lemma (in green_quadratic_character) green_paper_gram_archimedean_parameter:
  assumes even: "even cparam" and cge: "2 \<le> cparam"
    and large: "2 * cparam \<le> q ^ (cparam div 2)"
    and idxs: "distinct idxs"
      "set idxs = diagonal_grid (cpx_sqrt d)
        (natural_grid (green_N q cparam)) \<times> {..<green_J q cparam}"
  shows "ln (real_of_int (green_row_gram_determinant d
      (diagonal_grid (cpx_sqrt d) (natural_grid (green_N q cparam)))
      (green_J q cparam) (green_X q cparam) (green_J q cparam)))
    \<le> (1 / 2 + 11 / real cparam) *
      (real (green_X q cparam)) ^ 2 * real (green_J q cparam) *
      ln (real (green_X q cparam))"
proof -
  let ?X = "green_X q cparam"
  let ?J = "green_J q cparam"
  let ?N = "green_N q cparam"
  let ?x = "real ?X"
  let ?j = "real ?J"
  let ?c = "real cparam"
  let ?L = "ln (real q)"
  let ?M = "?x * ?j"
  let ?A = "2 * real (?N * ?N * ?J)"
  let ?B = "2 * real ?N * sqrt (real q)"
  let ?K = "4 * ?c + 2 * ?j * ?c + (?x + ?j) * (?c + 5) / 2"
  let ?D = "real_of_int (green_row_gram_determinant d
      (diagonal_grid (cpx_sqrt d) (natural_grid ?N)) ?J ?X ?J)"
  have qge: "2 \<le> q" using conductor_pos by linarith
  have Lnonneg: "0 \<le> ?L" using qge by simp
  have lnX: "ln ?x = ?c * ?L"
    using qge by (simp add: green_X_def ln_realpow)
  have Mcap: "0 \<le> ?M" by simp
  have first: "ln ?A \<le> 4 * ?c * ?L"
    using green_archimedean_paper_first_log[OF even cge large]
    by (simp add: lnX)
  have box: "ln ?B \<le> (?c + 5) / 2 * ?L"
    by (rule green_archimedean_log_box[OF qge even])
  have t1: "?M * ln ?A \<le> ?M * (4 * ?c * ?L)"
    by (rule mult_left_mono[OF first Mcap])
  have t3: "?M * (?x + ?j) * ln ?B \<le>
      ?M * (?x + ?j) * ((?c + 5) / 2 * ?L)"
    by (rule mult_left_mono[OF box]) simp
  have middle: "2 * ?j * ?M * ln ?x =
      ?M * (2 * ?j * ?c * ?L)"
    by (simp add: lnX algebra_simps)
  have logdet:
    "ln ?D \<le> ?M * ln ?A + 2 * ?j * ?M * ln ?x +
      ?M * (?x + ?j) * ln ?B"
    using green_paper_gram_archimedean_log[OF even cge large idxs]
    by simp
  have Hcap: "?M * ln ?A + 2 * ?j * ?M * ln ?x +
      ?M * (?x + ?j) * ln ?B \<le> ?M * ?K * ?L"
  proof -
    have "?M * ln ?A + 2 * ?j * ?M * ln ?x +
        ?M * (?x + ?j) * ln ?B \<le>
        ?M * (4 * ?c * ?L) + ?M * (2 * ?j * ?c * ?L) +
        ?M * (?x + ?j) * ((?c + 5) / 2 * ?L)"
      using t1 t3 middle by linarith
    also have "... = ?M * ?K * ?L"
      by (simp add: field_simps; algebra)
    finally show ?thesis .
  qed
  have square: "?X = (q ^ (cparam div 2)) * (q ^ (cparam div 2))"
    by (rule green_even_exponent_square[OF even])
  have tge: "2 * cparam \<le> q ^ (cparam div 2)" by (rule large)
  have tle: "q ^ (cparam div 2) \<le> ?X"
  proof -
    have "1 * q ^ (cparam div 2) \<le>
        q ^ (cparam div 2) * q ^ (cparam div 2)"
      by (rule mult_right_mono) (use tge cge in simp_all)
    then show ?thesis by (simp add: square)
  qed
  have xge: "?c \<le> ?x" using tge tle by linarith
  have jcap_nat: "cparam * ?J \<le> ?X"
  proof -
    have "?X div cparam * cparam \<le> ?X"
      using div_mult_mod_eq[of ?X cparam] by linarith
    then show ?thesis by (simp add: green_J_def mult.commute)
  qed
  have jcap: "?c * ?j \<le> ?x"
    using of_nat_mono[OF jcap_nat] by simp
  have coeff: "?K \<le> ?x * (?c + 22) / 2"
    by (rule green_archimedean_parameter_coefficient)
      (use cge xge jcap in simp_all)
  have scaled: "?M * ?K * ?L \<le>
      ?M * (?x * (?c + 22) / 2) * ?L"
  proof -
    have "?M * ?K \<le> ?M * (?x * (?c + 22) / 2)"
      by (rule mult_left_mono[OF coeff Mcap])
    then show ?thesis
      by (rule mult_right_mono[OF _ Lnonneg])
  qed
  have cne: "?c \<noteq> 0" using cge by simp
  have fraction: "(1 / 2 + 11 / ?c) * ?c = (?c + 22) / 2"
    using cne by (simp add: field_simps)
  have final_identity:
    "?M * (?x * (?c + 22) / 2) * ?L =
      (1 / 2 + 11 / ?c) * ?x\<^sup>2 * ?j * ln ?x"
    using fraction cne
    by (simp add: lnX power2_eq_square algebra_simps)
  show ?thesis
    using logdet Hcap scaled final_identity by linarith
qed

end
