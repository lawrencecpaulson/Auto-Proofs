(*  Title:      Gelfond_Schneider/Log_Values.thy
    Author:     OpenAI Codex

Basic infrastructure for treating complex logarithms and complex powers as
set-valued objects. This keeps branch choices explicit, which is convenient
for Baker-style and Gelfond-Schneider-style statements.
*)

theory Log_Values
  imports "Hermite_Lindemann.Hermite_Lindemann"
begin

section \<open>Set-Valued Logarithms and Powers\<close>

definition log_values :: "complex \<Rightarrow> complex set"
  where "log_values a = {z. exp z = a}"

definition power_values :: "complex \<Rightarrow> complex \<Rightarrow> complex set"
  where "power_values a b = {w. \<exists>z\<in>log_values a. w = exp (b * z)}"

definition complex_lincomb :: "complex list \<Rightarrow> complex list \<Rightarrow> complex"
  where "complex_lincomb cs xs = sum_list (map (\<lambda>(c, x). c * x) (zip cs xs))"

definition rat_lincomb :: "rat list \<Rightarrow> complex list \<Rightarrow> complex"
  where "rat_lincomb qs xs = complex_lincomb (map of_rat qs) xs"

definition rat_linearly_independent :: "complex list \<Rightarrow> bool"
  where
    "rat_linearly_independent xs \<longleftrightarrow>
      (\<forall>qs. length qs = length xs \<longrightarrow> rat_lincomb qs xs = 0 \<longrightarrow> (\<forall>q\<in>set qs. q = 0))"

lemma mem_log_values_iff [simp]:
  "z \<in> log_values a \<longleftrightarrow> exp z = a"
  by (simp add: log_values_def)

lemma mem_power_values_iff:
  "w \<in> power_values a b \<longleftrightarrow> (\<exists>z. z \<in> log_values a \<and> w = exp (b * z))"
  by (auto simp: power_values_def)

lemma zero_in_log_values_iff [simp]:
  "0 \<in> log_values a \<longleftrightarrow> a = 1"
  by (simp add: log_values_def)

lemma Ln_in_log_values [intro]:
  assumes "a \<noteq> 0"
  shows "Ln a \<in> log_values a"
  using assms by (simp add: log_values_def)

lemma log_values_nonempty_iff [simp]:
  "log_values a \<noteq> {} \<longleftrightarrow> a \<noteq> 0"
proof
  assume "log_values a \<noteq> {}"
  then obtain z where "z \<in> log_values a"
    by blast
  then show "a \<noteq> 0"
    by auto
next
  assume "a \<noteq> 0"
  then show "log_values a \<noteq> {}"
    using Ln_in_log_values by blast
qed

lemma power_values_nonempty_iff [simp]:
  "power_values a b \<noteq> {} \<longleftrightarrow> a \<noteq> 0"
proof
  assume "power_values a b \<noteq> {}"
  then obtain w where "w \<in> power_values a b"
    by blast
  then obtain z where "z \<in> log_values a"
    by (auto simp: power_values_def)
  then show "a \<noteq> 0"
    by auto
next
  assume "a \<noteq> 0"
  then have "exp (b * Ln a) \<in> power_values a b"
    by (auto simp: power_values_def)
  then show "power_values a b \<noteq> {}"
    by blast
qed

lemma principal_power_value_mem [intro]:
  assumes "a \<noteq> 0"
  shows "exp (b * Ln a) \<in> power_values a b"
  using assms by (auto simp: power_values_def)

lemma power_values_nonzero:
  assumes "w \<in> power_values a b"
  shows "w \<noteq> 0"
  using assms by (auto simp: power_values_def)

lemma complex_lincomb_Nil_right [simp]:
  "complex_lincomb cs [] = 0"
  by (simp add: complex_lincomb_def)

lemma complex_lincomb_Nil_left [simp]:
  "complex_lincomb [] xs = 0"
  by (simp add: complex_lincomb_def)

lemma complex_lincomb_Cons_Cons [simp]:
  "complex_lincomb (c # cs) (x # xs) = c * x + complex_lincomb cs xs"
  by (simp add: complex_lincomb_def)

lemma complex_lincomb_pair [simp]:
  "complex_lincomb [c1, c2] [x1, x2] = c1 * x1 + c2 * x2"
  by simp

lemma complex_lincomb_snoc_snoc:
  assumes "length cs = length xs"
  shows "complex_lincomb (cs @ [c]) (xs @ [x]) = complex_lincomb cs xs + c * x"
  using assms by (simp add: complex_lincomb_def)

lemma complex_lincomb_append:
  assumes "length cs1 = length xs1"
  shows "complex_lincomb (cs1 @ cs2) (xs1 @ xs2) = complex_lincomb cs1 xs1 + complex_lincomb cs2 xs2"
  using assms
  by (induction cs1 xs1 rule: list_induct2) (simp_all add: algebra_simps)

lemma complex_lincomb_map_scale_left:
  assumes "length cs = length xs"
  shows "complex_lincomb (map (\<lambda>c. k * c) cs) xs = k * complex_lincomb cs xs"
  using assms by (induction cs xs rule: list_induct2) (simp_all add: algebra_simps)

lemma complex_lincomb_map2_add_left:
  assumes "length cs = length xs"
  assumes "length ds = length xs"
  shows "complex_lincomb (map2 (+) cs ds) xs = complex_lincomb cs xs + complex_lincomb ds xs"
  using assms
proof (induction cs xs arbitrary: ds rule: list_induct2)
  case Nil
  then show ?case
    by (cases ds) simp_all
next
  case (Cons c cs x xs)
  then obtain d ds' where ds: "ds = d # ds'"
    by (cases ds) auto
  show ?case
    using Cons ds by (simp add: algebra_simps)
qed

lemma complex_lincomb_zero_left:
  assumes "length cs = length xs"
  assumes "\<forall>c\<in>set cs. c = 0"
  shows "complex_lincomb cs xs = 0"
  using assms
  by (induction cs xs rule: list_induct2) auto

lemma rat_lincomb_Cons_Cons [simp]:
  "rat_lincomb (q # qs) (x # xs) = of_rat q * x + rat_lincomb qs xs"
  by (simp add: rat_lincomb_def)

lemma rat_lincomb_Nil_left [simp]:
  "rat_lincomb [] xs = 0"
  by (simp add: rat_lincomb_def)

lemma rat_lincomb_Nil_right [simp]:
  "rat_lincomb qs [] = 0"
  by (simp add: rat_lincomb_def)

lemma rat_lincomb_pair [simp]:
  "rat_lincomb [q1, q2] [x1, x2] = of_rat q1 * x1 + of_rat q2 * x2"
  by simp

lemma rat_lincomb_snoc_snoc:
  assumes "length qs = length xs"
  shows "rat_lincomb (qs @ [q]) (xs @ [x]) = rat_lincomb qs xs + of_rat q * x"
  using assms by (simp add: rat_lincomb_def complex_lincomb_snoc_snoc)

lemma rat_lincomb_append:
  assumes "length qs1 = length xs1"
  shows "rat_lincomb (qs1 @ qs2) (xs1 @ xs2) = rat_lincomb qs1 xs1 + rat_lincomb qs2 xs2"
  using assms by (simp add: rat_lincomb_def complex_lincomb_append)

lemma rat_lincomb_map_scale_left:
  assumes "length qs = length xs"
  shows "rat_lincomb (map ((*) r) qs) xs = of_rat r * rat_lincomb qs xs"
  using assms
  by (induction qs xs rule: list_induct2) (simp_all add: algebra_simps of_rat_mult)

lemma rat_lincomb_map2_add_left:
  assumes "length qs = length xs"
  assumes "length rs = length xs"
  shows "rat_lincomb (map2 (+) qs rs) xs = rat_lincomb qs xs + rat_lincomb rs xs"
  using assms
proof (induction qs xs arbitrary: rs rule: list_induct2)
  case Nil
  then show ?case
    by (cases rs) simp_all
next
  case (Cons q qs x xs)
  then obtain r rs' where rs: "rs = r # rs'"
    by (cases rs) auto
  show ?case
    using Cons rs by (simp add: algebra_simps of_rat_add)
qed

lemma rat_linearly_independent_Nil [simp]:
  "rat_linearly_independent []"
  by (auto simp: rat_linearly_independent_def rat_lincomb_def complex_lincomb_def)

lemma rat_linearly_independent_ConsD:
  assumes "rat_linearly_independent (x # xs)"
  shows "rat_linearly_independent xs"
proof (unfold rat_linearly_independent_def, intro allI impI)
  fix qs :: "rat list"
  assume len: "length qs = length xs"
  assume rel: "rat_lincomb qs xs = 0"
  have len': "length (0 # qs) = length (x # xs)"
    using len by simp
  have rel': "rat_lincomb (0 # qs) (x # xs) = 0"
    using rel by simp
  have zeros: "\<forall>q\<in>set (0 # qs). q = 0"
    using assms len' rel' unfolding rat_linearly_independent_def by blast
  then show "\<forall>q\<in>set qs. q = 0"
    by simp
qed

lemma rat_linearly_independent_snocD:
  assumes "rat_linearly_independent (xs @ [x])"
  shows "rat_linearly_independent xs"
proof (unfold rat_linearly_independent_def, intro allI impI)
  fix qs :: "rat list"
  assume len: "length qs = length xs"
  assume rel: "rat_lincomb qs xs = 0"
  have len': "length (qs @ [0]) = length (xs @ [x])"
    using len by simp
  have rel': "rat_lincomb (qs @ [0]) (xs @ [x]) = 0"
    using len rel by (simp add: rat_lincomb_snoc_snoc)
  have zeros: "\<forall>q\<in>set (qs @ [0]). q = 0"
    using assms len' rel' unfolding rat_linearly_independent_def by blast
  then show "\<forall>q\<in>set qs. q = 0"
    by simp
qed

lemma rat_linearly_independent_snoc_rational_shift:
  assumes indep: "rat_linearly_independent (xs @ [x])"
  assumes len: "length rs = length xs"
  shows "rat_linearly_independent (xs @ [x + rat_lincomb rs xs])"
proof (unfold rat_linearly_independent_def, intro allI impI)
  fix qs :: "rat list"
  assume len_qs: "length qs = length (xs @ [x + rat_lincomb rs xs])"
  assume rel: "rat_lincomb qs (xs @ [x + rat_lincomb rs xs]) = 0"
  from len_qs obtain qs0 t where qs: "qs = qs0 @ [t]"
    by (cases qs rule: rev_cases) auto
  have len_qs0: "length qs0 = length xs"
    using len_qs qs by simp
  have rel':
      "rat_lincomb (map2 (+) qs0 (map ((*) t) rs) @ [t]) (xs @ [x]) = 0"
  proof -
    have "rat_lincomb (map2 (+) qs0 (map ((*) t) rs) @ [t]) (xs @ [x]) =
          rat_lincomb (map2 (+) qs0 (map ((*) t) rs)) xs + of_rat t * x"
      using len_qs0 len by (simp add: rat_lincomb_snoc_snoc)
    also have "\<dots> = rat_lincomb qs0 xs + rat_lincomb (map ((*) t) rs) xs + of_rat t * x"
      using len_qs0 len by (simp add: rat_lincomb_map2_add_left algebra_simps)
    also have "\<dots> = rat_lincomb qs0 xs + of_rat t * rat_lincomb rs xs + of_rat t * x"
      using len by (simp add: rat_lincomb_map_scale_left algebra_simps)
    also have "\<dots> = rat_lincomb qs0 xs + of_rat t * (x + rat_lincomb rs xs)"
      by (simp add: algebra_simps)
    also have "\<dots> = rat_lincomb qs (xs @ [x + rat_lincomb rs xs])"
      using len_qs0 qs by (simp add: rat_lincomb_snoc_snoc algebra_simps)
    finally show ?thesis
      using rel by simp
  qed
  have len':
      "length (map2 (+) qs0 (map ((*) t) rs) @ [t]) = length (xs @ [x])"
    using len_qs0 len by simp
  have zeros:
      "\<forall>q\<in>set (map2 (+) qs0 (map ((*) t) rs) @ [t]). q = 0"
    using indep len' rel' unfolding rat_linearly_independent_def by blast
  have t0: "t = 0"
    using zeros by simp
  have zeros0: "\<forall>q\<in>set qs0. q = 0"
  proof -
    have map_zero: "map ((*) t) rs = replicate (length qs0) 0"
    proof -
      have "map ((*) t) rs = replicate (length rs) 0"
        using t0 by (induction rs) simp_all
      also have "... = replicate (length qs0) 0"
        using len_qs0 len by simp
      finally show ?thesis .
    qed
    have "map2 (+) qs0 (map ((*) t) rs) = qs0"
    proof -
      have "map2 (+) qs0 (replicate (length qs0) 0) = qs0"
        by (induction qs0) simp_all
      with map_zero show ?thesis
        by simp
    qed
    with zeros show ?thesis
      by simp
  qed
  show "\<forall>q\<in>set qs. q = 0"
    using zeros0 t0 qs by auto
qed

lemma rat_linearly_independent_drop_middle:
  assumes indep: "rat_linearly_independent (xs @ y # ys)"
  shows "rat_linearly_independent (xs @ ys)"
proof (unfold rat_linearly_independent_def, intro allI impI)
  fix qs :: "rat list"
  assume len: "length qs = length (xs @ ys)"
  assume rel: "rat_lincomb qs (xs @ ys) = 0"
  define qsL where "qsL = take (length xs) qs"
  define qsR where "qsR = drop (length xs) qs"
  have qs_split: "qs = qsL @ qsR"
    by (simp add: qsL_def qsR_def)
  have lenL: "length qsL = length xs"
    by (simp add: qsL_def len)
  have lenR: "length qsR = length ys"
    by (simp add: qsR_def len)
  define qs' where "qs' = qsL @ 0 # qsR"
  have len': "length qs' = length (xs @ y # ys)"
    using lenL lenR by (simp add: qs'_def)
  have rel': "rat_lincomb qs' (xs @ y # ys) = 0"
  proof -
    have "rat_lincomb qs' (xs @ y # ys) =
          rat_lincomb qsL xs + rat_lincomb (0 # qsR) (y # ys)"
      using lenL by (simp add: qs'_def rat_lincomb_append)
    also have "\<dots> = rat_lincomb qsL xs + rat_lincomb qsR ys"
      by simp
    also have "\<dots> = rat_lincomb qs (xs @ ys)"
      using lenL qs_split by (simp add: rat_lincomb_append)
    finally show ?thesis
      using rel by simp
  qed
  have zeros: "\<forall>q\<in>set qs'. q = 0"
    using indep len' rel' unfolding rat_linearly_independent_def by blast
  show "\<forall>q\<in>set qs. q = 0"
    using zeros qs_split by (auto simp: qs'_def)
qed

lemma rat_linearly_independent_append_pair_tailD:
  assumes "rat_linearly_independent (xs @ [y, z])"
  shows "rat_linearly_independent [y, z]"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "rat_linearly_independent (x # (xs @ [y, z]))"
    using Cons.prems by simp
  then have "rat_linearly_independent (xs @ [y, z])"
    by (rule rat_linearly_independent_ConsD)
  then show ?case
    by (rule Cons.IH)
qed

lemma rat_linearly_independent_middle_last:
  assumes indep: "rat_linearly_independent (xs @ y # ys @ [z])"
  shows "rat_linearly_independent [y, z]"
  using indep
proof (induction ys arbitrary: xs)
  case Nil
  then show ?case
    by (simp add: rat_linearly_independent_append_pair_tailD)
next
  case (Cons y' ys)
  have indep_tmp: "rat_linearly_independent ((xs @ [y]) @ (y' # (ys @ [z])))"
    using Cons.prems by simp
  have indep': "rat_linearly_independent ((xs @ [y]) @ ys @ [z])"
    by (rule rat_linearly_independent_drop_middle[OF indep_tmp])
  have indep'': "rat_linearly_independent (xs @ y # ys @ [z])"
    using indep' by simp
  then have "rat_linearly_independent [y, z]"
    by (rule Cons.IH)
  then show ?case .
qed

lemma rat_linearly_independent_singleton:
  "rat_linearly_independent [z] \<longleftrightarrow> z \<noteq> 0"
proof
  assume indep: "rat_linearly_independent [z]"
  show "z \<noteq> 0"
  proof
    assume "z = 0"
    then have "rat_lincomb [1] [z] = 0"
      by (simp add: rat_lincomb_def complex_lincomb_def)
    moreover have "length ([1] :: rat list) = length [z]"
      by simp
    ultimately have "\<forall>q\<in>set ([1] :: rat list). q = 0"
      using indep unfolding rat_linearly_independent_def by blast
    then have "1 = (0 :: rat)"
      by simp
    then show False by simp
  qed
next
  assume nz: "z \<noteq> 0"
  show "rat_linearly_independent [z]"
  proof (unfold rat_linearly_independent_def, intro allI impI)
    fix qs :: "rat list"
    assume len: "length qs = length [z]"
    assume rel: "rat_lincomb qs [z] = 0"
    from len obtain q where qs: "qs = [q]"
      by (cases qs) auto
    with rel nz show "\<forall>q\<in>set qs. q = 0"
      by (simp add: rat_lincomb_def complex_lincomb_def)
  qed
qed

lemma rat_linearly_independent_pair_scale:
  fixes z b :: complex
  assumes z: "z \<noteq> 0"
  assumes b: "b \<notin> \<rat>"
  shows "rat_linearly_independent [z, b * z]"
proof (unfold rat_linearly_independent_def, intro allI impI)
  fix qs :: "rat list"
  assume len: "length qs = length [z, b * z]"
  assume rel: "rat_lincomb qs [z, b * z] = 0"
  from len obtain q1 rest where qs1: "qs = q1 # rest"
    by (cases qs) auto
  from len qs1 obtain q2 where qs: "qs = [q1, q2]"
    by (cases rest) auto
  show "\<forall>q\<in>set qs. q = 0"
  proof (cases "q2 = 0")
    case True
    with rel qs z have "q1 = 0"
      by simp
    with True qs show ?thesis
      by simp
  next
    case False
    have coeff0: "of_rat q1 + of_rat q2 * b = 0"
    proof -
      have "(of_rat q1 + of_rat q2 * b) * z = 0"
        using rel qs by (simp add: algebra_simps)
      with z show ?thesis
        by simp
    qed
    have "of_rat q2 * b = - of_rat q1"
      using coeff0 by (simp add: add_eq_0_iff)
    hence "b * of_rat q2 = - of_rat q1"
      by (simp add: mult.commute)
    then have "b = (- of_rat q1) / of_rat q2"
      using False by (simp add: field_simps)
    also have "\<dots> = - (of_rat q1 / of_rat q2)"
      by (simp add: divide_minus_left)
    also have "\<dots> = - of_rat (q1 / q2)"
      by (simp add: of_rat_divide)
    also have "\<dots> = of_rat (-q1 / q2)"
      by (simp add: of_rat_minus)
    finally have "b = of_rat (-q1 / q2)" .
    hence "b \<in> \<rat>"
      unfolding Rats_def by blast
    with b show ?thesis
      by contradiction
  qed
qed


lemma rat_linearly_independent_pairD1:
  assumes "rat_linearly_independent [z1, z2]"
  shows "z1 \<noteq> 0"
proof
  assume z1: "z1 = 0"
  have "rat_lincomb [1, 0] [z1, z2] = 0"
    using z1 by simp
  moreover have "length ([1, 0] :: rat list) = length [z1, z2]"
    by simp
  ultimately have "\<forall>q\<in>set ([1, 0] :: rat list). q = 0"
    using assms unfolding rat_linearly_independent_def by blast
  then show False
    by simp
qed

lemma rat_linearly_independent_pairD2:
  assumes "rat_linearly_independent [z1, z2]"
  shows "z2 \<noteq> 0"
proof
  assume z2: "z2 = 0"
  have "rat_lincomb [0, 1] [z1, z2] = 0"
    using z2 by simp
  moreover have "length ([0, 1] :: rat list) = length [z1, z2]"
    by simp
  ultimately have "\<forall>q\<in>set ([0, 1] :: rat list). q = 0"
    using assms unfolding rat_linearly_independent_def by blast
  then show False
    by simp
qed

end
