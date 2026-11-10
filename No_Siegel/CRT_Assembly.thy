theory CRT_Assembly
  imports Prime_Power_Values
begin

unbundle no vec_lambda_syntax

text \<open>Green, Section 2: assembly of Dirichlet characters by the Chinese remainder theorem.\<close>

definition crt_lift :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "crt_lift m k a = (SOME x. [x = a] (mod m) \<and> [x = 1] (mod k))"

lemma crt_lift_conditions:
  assumes "coprime m k"
  shows "[crt_lift m k a = a] (mod m) \<and>
    [crt_lift m k a = 1] (mod k)"
proof -
  have ex: "\<exists>x. [x = a] (mod m) \<and> [x = 1] (mod k)"
    by (rule binary_chinese_remainder_nat[OF assms])
  have "[(SOME x. [x = a] (mod m) \<and> [x = 1] (mod k)) = a] (mod m) \<and>
    [(SOME x. [x = a] (mod m) \<and> [x = 1] (mod k)) = 1] (mod k)"
    by (rule someI_ex[OF ex])
  then show ?thesis by (simp add: crt_lift_def)
qed

lemma crt_lift_left:
  assumes "coprime m k"
  shows "[crt_lift m k a = a] (mod m)"
  using crt_lift_conditions[OF assms] by blast

lemma crt_lift_right:
  assumes "coprime m k"
  shows "[crt_lift m k a = 1] (mod k)"
  using crt_lift_conditions[OF assms] by blast

lemma crt_lift_cong:
  assumes "coprime m k" "[a = b] (mod m)"
  shows "[crt_lift m k a = crt_lift m k b] (mod m * k)"
  by (rule coprime_cong_mult_nat)
    (use assms crt_lift_left[OF assms(1)] crt_lift_right[OF assms(1)] in \<open>auto simp: cong_def\<close>)

lemma crt_lift_mult:
  assumes cp: "coprime m k"
  shows "[crt_lift m k (a * b) = crt_lift m k a * crt_lift m k b] (mod m * k)"
proof (rule coprime_cong_mult_nat[OF _ _ cp])
  have "[crt_lift m k (a * b) = a * b] (mod m)"
    by (rule crt_lift_left[OF cp])
  moreover have "[crt_lift m k a * crt_lift m k b = a * b] (mod m)"
    by (intro cong_mult crt_lift_left[OF cp])
  ultimately show "[crt_lift m k (a * b) = crt_lift m k a * crt_lift m k b] (mod m)"
    by (meson cong_sym cong_trans)
  have "[crt_lift m k (a * b) = 1] (mod k)"
    by (rule crt_lift_right[OF cp])
  moreover have "[crt_lift m k a * crt_lift m k b = 1 * 1] (mod k)"
    by (intro cong_mult crt_lift_right[OF cp])
  ultimately show "[crt_lift m k (a * b) = crt_lift m k a * crt_lift m k b] (mod k)"
    by (simp add: cong_def)
qed

lemma crt_lift_one:
  assumes "coprime m k"
  shows "[crt_lift m k 1 = 1] (mod m * k)"
  by (intro coprime_cong_mult_nat crt_lift_left[OF assms]
    crt_lift_right[OF assms] assms)

locale crt_dcharacter = dcharacter +
  fixes m k :: nat
  assumes factor_modulus: "n = m * k"
    and factors_coprime: "coprime m k"
    and m_gt_one: "1 < m" and k_gt_one: "1 < k"
begin

abbreviation chi_left where "chi_left a \<equiv> \<chi> (crt_lift m k a)"
abbreviation chi_right where "chi_right a \<equiv> \<chi> (crt_lift k m a)"

lemma chi_left_cong:
  assumes "[a = b] (mod m)"
  shows "chi_left a = chi_left b"
  by (rule cong) (simp add: factor_modulus crt_lift_cong[OF factors_coprime assms])

lemma chi_left_mult: "chi_left (a * b) = chi_left a * chi_left b"
  using crt_lift_mult[OF factors_coprime, of a b]
  by (metis cong mult factor_modulus)

lemma chi_left_one: "chi_left 1 = 1"
proof -
  have lift: "[crt_lift m k 1 = 1] (mod n)"
    unfolding factor_modulus by (rule crt_lift_one[OF factors_coprime])
  have "chi_left 1 = \<chi> 1" by (rule cong[OF lift])
  then show ?thesis by simp
qed

lemma chi_left_zero:
  assumes "\<not> coprime a m"
  shows "chi_left a = 0"
proof -
  have "\<not> coprime (crt_lift m k a) m"
    using assms crt_lift_left[OF factors_coprime, of a]
    by (simp add: coprime_cong_cong_left)
  then have "\<not> coprime (crt_lift m k a) (m * k)" by simp
  then have "\<not> coprime (crt_lift m k a) n"
    by (simp add: factor_modulus)
  then show ?thesis by (rule eq_zero)
qed

lemma chi_left_dcharacter: "dcharacter m chi_left"
proof (unfold_locales)
  show "1 < m" by (rule m_gt_one)
  fix a b
  assume "a \<in> totatives m" "b \<in> totatives m"
  show "chi_left (a * b) = chi_left a * chi_left b"
    by (rule chi_left_mult)
next
  fix a
  assume "\<not> coprime a m"
  then show "chi_left a = 0" by (rule chi_left_zero)
next
  fix a
  show "chi_left (a + m) = chi_left a"
    by (rule chi_left_cong) (simp add: cong_def)
next
  show "chi_left 1 \<noteq> 0" using chi_left_one by simp
qed

lemma chi_right_dcharacter: "dcharacter k chi_right"
proof -
  interpret swapped: crt_dcharacter n "residue_mult_group n" \<chi> k m
    by (unfold_locales; use factor_modulus factors_coprime m_gt_one k_gt_one in
      \<open>auto simp: mult.commute coprime_commute\<close>)
  show ?thesis by (rule swapped.chi_left_dcharacter)
qed

lemma factorization: "\<chi> a = chi_left a * chi_right a"
proof -
  have cp_rev: "coprime k m"
    using factors_coprime by (simp add: coprime_commute)
  have liftprod: "[crt_lift m k a * crt_lift k m a = a] (mod n)"
  proof (unfold factor_modulus, rule coprime_cong_mult_nat[OF _ _ factors_coprime])
    have "[crt_lift m k a * crt_lift k m a = a * 1] (mod m)"
      by (intro cong_mult crt_lift_left[OF factors_coprime]
        crt_lift_right[OF cp_rev])
    then show "[crt_lift m k a * crt_lift k m a = a] (mod m)" by simp
    have "[crt_lift m k a * crt_lift k m a = 1 * a] (mod k)"
      by (intro cong_mult crt_lift_right[OF factors_coprime]
        crt_lift_left[OF cp_rev])
    then show "[crt_lift m k a * crt_lift k m a = a] (mod k)" by simp
  qed
  have "\<chi> a = \<chi> (crt_lift m k a * crt_lift k m a)"
    by (rule cong) (rule cong_sym[OF liftprod])
  then show ?thesis by simp
qed

lemma chi_left_primitive:
  assumes primitive: "primitive_dchar n \<chi>"
  shows "primitive_dchar m chi_left"
proof -
  interpret L: dcharacter m "residue_mult_group m" chi_left
    by (rule chi_left_dcharacter)
  interpret R: dcharacter k "residue_mult_group k" chi_right
    by (rule chi_right_dcharacter)
  have n_primitive: "\<not> (\<exists>d<n. induced_modulus d)"
    using primitive primitive_dchar_iff by simp
  show ?thesis
  proof (rule L.primitive_dchar_iff[THEN iffD2])
    show "\<not> (\<exists>d<m. L.induced_modulus d)"
    proof
      assume "\<exists>d<m. L.induced_modulus d"
      then obtain d where dlt: "d < m" and induced: "L.induced_modulus d" by blast
      have ddvd: "d dvd m" by (rule L.induced_modulus_dvd[OF induced])
      have dprod_lt: "d * k < n"
        using dlt k_gt_one by (simp add: factor_modulus)
      have "induced_modulus (d * k)"
      proof (rule induced_modulusI)
        show "d * k dvd n" using ddvd by (simp add: factor_modulus)
        fix a
        assume acp: "coprime a n" and acong: "[a = 1] (mod d * k)"
        have acpm: "coprime a m" using acp by (simp add: factor_modulus)
        have ad: "[a = 1] (mod d)"
          using acong by (rule cong_dvd_mono_modulus) simp
        have ak: "[a = 1] (mod k)"
          using acong by (rule cong_dvd_mono_modulus) simp
        have "chi_left a = 1" by (rule L.induced_modulusD[OF induced acpm ad])
        moreover have "chi_right a = 1" using R.cong[OF ak] by simp
        ultimately show "\<chi> a = 1" using factorization[of a] by simp
      qed
      with dprod_lt n_primitive show False by blast
    qed
  qed
qed

lemma chi_right_primitive:
  assumes "primitive_dchar n \<chi>"
  shows "primitive_dchar k chi_right"
proof -
  interpret swapped: crt_dcharacter n "residue_mult_group n" \<chi> k m
    by (unfold_locales; use factor_modulus factors_coprime m_gt_one k_gt_one in
      \<open>auto simp: mult.commute coprime_commute\<close>)
  show ?thesis by (rule swapped.chi_left_primitive[OF assms])
qed

lemma chi_left_real:
  assumes real: "real_dcharacter n \<chi>"
  shows "real_dcharacter m chi_left"
proof -
  interpret R: real_dcharacter n "residue_mult_group n" \<chi>
    by (rule real)
  show ?thesis
    using chi_left_dcharacter R.real
    unfolding real_dcharacter_def real_dcharacter_axioms_def by blast
qed

lemma chi_right_real:
  assumes "real_dcharacter n \<chi>"
  shows "real_dcharacter k chi_right"
proof -
  interpret swapped: crt_dcharacter n "residue_mult_group n" \<chi> k m
    by (unfold_locales; use factor_modulus factors_coprime m_gt_one k_gt_one in
      \<open>auto simp: mult.commute coprime_commute\<close>)
  show ?thesis by (rule swapped.chi_left_real[OF assms])
qed

end

context green_primitive_real_dcharacter
begin

lemma crt_green_factors:
  assumes nr: "n = m * k" and cp: "coprime m k"
    and mgt: "1 < m" and kgt: "1 < k"
  obtains psi theta where
    "green_primitive_real_dcharacter m psi"
    "green_primitive_real_dcharacter k theta"
    "\<And>a. \<chi> a = psi a * theta a"
proof -
  interpret C: crt_dcharacter n "residue_mult_group n" \<chi> m k
    by (unfold_locales; use nr cp mgt kgt in \<open>auto\<close>)
  have source_real: "real_dcharacter n \<chi>"
    using dcharacter_axioms real_dcharacter_axioms
    unfolding real_dcharacter_def by blast
  have source_primitive: "primitive_dchar n \<chi>"
    using dcharacter_axioms primitive_dchar_axioms
    unfolding primitive_dchar_def by blast
  have left_real: "real_dcharacter m C.chi_left"
    by (rule C.chi_left_real[OF source_real])
  have left_primitive: "primitive_dchar m C.chi_left"
    by (rule C.chi_left_primitive[OF source_primitive])
  have left_green: "green_primitive_real_dcharacter m C.chi_left"
    using left_real left_primitive
    unfolding green_primitive_real_dcharacter_def by blast
  have right_real: "real_dcharacter k C.chi_right"
    by (rule C.chi_right_real[OF source_real])
  have right_primitive: "primitive_dchar k C.chi_right"
    by (rule C.chi_right_primitive[OF source_primitive])
  have right_green: "green_primitive_real_dcharacter k C.chi_right"
    using right_real right_primitive
    unfolding green_primitive_real_dcharacter_def by blast
  show thesis
    by (rule that[OF left_green right_green C.factorization])
qed

end

end
