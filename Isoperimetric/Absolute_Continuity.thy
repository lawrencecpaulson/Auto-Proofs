theory Absolute_Continuity
  imports Bounded_Variation 
Isar_Explore
 "HOL-ex.Sketch_and_Explore" 
begin

text \<open>
  Absolute continuity for functions @{typ "real \<Rightarrow> 'a::euclidean_space"},
  following HOL Light's @{text "Multivariate/integration.ml"} (lines 22442--23825)
  and the fundamental theorem of calculus for absolutely continuous functions
  from @{text "Multivariate/measure.ml"} (line 24882).

  In HOL Light, @{text "absolutely_continuous_on"} is defined via
  @{text "absolutely_setcontinuous_on"} applied to the increment function.
  We give an equivalent direct \<open>\<epsilon>\<close>-\<open>\<delta>\<close> formulation.
\<close>

section \<open>Absolute set-continuity\<close>

definition absolutely_setcontinuous_on ::
  "(real set \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real set \<Rightarrow> bool" where
  "absolutely_setcontinuous_on f s \<longleftrightarrow>
    (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> s \<and>
      (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow> (\<Sum>k\<in>d. norm (f k)) < \<epsilon>)"

lemma absolutely_setcontinuous_on_imp_has_bounded_setvariation_on:
  fixes f :: "real set \<Rightarrow> 'a::euclidean_space"
  assumes "operative (+) 0 f"
    "absolutely_setcontinuous_on f s"
    "bounded s"
  shows "has_bounded_setvariation_on f s"
proof -
  from assms(2)[unfolded absolutely_setcontinuous_on_def, rule_format, OF zero_less_one]
  obtain r where r_pos: \<open>r > 0\<close>
    and r_bound: \<open>\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow> (\<Sum>k\<in>d. content k) < r \<Longrightarrow> (\<Sum>k\<in>d. norm (f k)) < 1\<close>
    by meson
  from \<open>bounded s\<close> obtain a :: real where s_sub: \<open>s \<subseteq> cbox (-a) a\<close>
    using bounded_subset_cbox_symmetric by blast
  define \<delta> where \<open>\<delta> = min r 1 / 3\<close>
  have \<delta>_pos: \<open>\<delta> > 0\<close> unfolding \<delta>_def using r_pos by auto
  obtain p where p_div: \<open>p tagged_division_of {-a..a}\<close> and p_fine: \<open>(\<lambda>x. ball x \<delta>) fine p\<close>
    using fine_division_exists_real[OF gauge_ball[OF \<delta>_pos]] by blast
  define D where \<open>D \<equiv> snd ` p\<close>
  have D_div: \<open>D division_of {-a..a}\<close>
    unfolding D_def using division_of_tagged_division[OF p_div] by simp
  have "(\<Sum>k\<in>d. norm (f k)) \<le> card D * 1"
    if div: "d division_of t" and sub: "t \<subseteq> s" for d t
  proof -
    have t_sub: "t \<subseteq> cbox (-a) a"
      using sub s_sub by auto
    \<comment> \<open>First inequality: pointwise bound via operative splitting\<close>
    have step1: "(\<Sum>k\<in>d. norm (f k)) \<le> (\<Sum>k\<in>d. \<Sum>l\<in>D. norm (f (k \<inter> l)))"
    proof (rule sum_mono)
      fix k assume kd: "k \<in> d"
      then obtain c' d' where k_eq: "k = cbox c' d'"
        using division_ofD(4)[OF div] by blast
      have k_ne: "k \<noteq> {}"
        using division_ofD(3)[OF div kd] by auto
      have k_sub: "k \<subseteq> cbox (-a) a"
        using division_ofD(2)[OF div kd] t_sub by auto
      \<comment> \<open>The intersections @{term \<open>{k \<inter> l | l. l \<in> D \<and> k \<inter> l \<noteq> {}}\<close>} form a division of @{term k}\<close>
      have k_div_self: "{cbox c' d'} division_of cbox c' d'"
        by (metis k_ne k_eq division_of_self)
      have inter_div: "{k1 \<inter> k2 |k1 k2. k1 \<in> {cbox c' d'} \<and> k2 \<in> D \<and> k1 \<inter> k2 \<noteq> {}}
                       division_of (cbox c' d' \<inter> cbox (-a) a)"
        using division_inter[OF k_div_self D_div] by auto
      have k_inter: "cbox c' d' \<inter> cbox (-a) a = cbox c' d'"
        using k_sub k_eq by blast
      then have E_div: "{cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}}
                        division_of cbox c' d'"
        using inter_div by auto
      \<comment> \<open>By operativity, @{term \<open>f k\<close>} equals the sum of @{term f} over the division\<close>
      have f_split: "sum f {cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}} = f (cbox c' d')"
        using operative.division[OF assms(1) E_div] by (simp add: sum_def)
      \<comment> \<open>Triangle inequality\<close>
      have step_eq: "norm (f k) = norm (sum f {cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}})"
        by (metis f_split k_eq)
      have step_tri: "norm (sum f {cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}})
                     \<le> (\<Sum>j\<in>{cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}}. norm (f j))"
        by (rule norm_sum)
      \<comment> \<open>Extend the sum from the image to all of @{term D} via @{thm sum_image_le}\<close>
      have step_img: "(\<Sum>j\<in>{cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}}. norm (f j))
                     \<le> (\<Sum>l\<in>{l \<in> D. cbox c' d' \<inter> l \<noteq> {}}. norm (f (cbox c' d' \<inter> l)))"
      proof -
        have finD: "finite D" using division_ofD(1)[OF D_div] by auto
        then have fin: "finite {l \<in> D. cbox c' d' \<inter> l \<noteq> {}}" by auto
        have eq: "(\<lambda>l. cbox c' d' \<inter> l) ` {l \<in> D. cbox c' d' \<inter> l \<noteq> {}}
                 = {cbox c' d' \<inter> l |l. l \<in> D \<and> cbox c' d' \<inter> l \<noteq> {}}"
          by auto
        show ?thesis unfolding eq[symmetric]
          by (intro order_trans[OF sum_image_le[OF fin]]) (auto simp: o_def)
      qed
      have step_ext: "(\<Sum>l\<in>{l \<in> D. cbox c' d' \<inter> l \<noteq> {}}. norm (f (cbox c' d' \<inter> l)))
                     \<le> (\<Sum>l\<in>D. norm (f (cbox c' d' \<inter> l)))"
        by (rule sum_mono2[OF division_ofD(1)[OF D_div]]) auto
      have step_rw: "(\<Sum>l\<in>D. norm (f (cbox c' d' \<inter> l))) = (\<Sum>l\<in>D. norm (f (k \<inter> l)))"
        by (simp add: k_eq)
      show "norm (f k) \<le> (\<Sum>l\<in>D. norm (f (k \<inter> l)))"
        using step_eq step_tri step_img step_ext step_rw by linarith
    qed
    \<comment> \<open>Second inequality: swap sums and bound each inner sum by 1\<close>
    also have "(\<Sum>k\<in>d. \<Sum>l\<in>D. norm (f (k \<inter> l))) = (\<Sum>l\<in>D. \<Sum>k\<in>d. norm (f (k \<inter> l)))"
      by (rule sum.swap)
    also have "\<dots> \<le> card D * 1"
    proof -
      have "(\<Sum>l\<in>D. \<Sum>k\<in>d. norm (f (k \<inter> l))) \<le> of_nat (card D) * 1"
      proof (rule sum_bounded_above)
        fix l assume lD: "l \<in> D"
        then obtain u v where luv: \<open>l = {u..v}\<close> and \<open>{u..v} \<in> D\<close> \<open>{u..v} \<noteq> {}\<close>
          by (metis D_div cbox_division_memE cbox_interval)
        define d' where \<open>d' \<equiv> (\<lambda>k. k \<inter> {u..v}) ` {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close>
        have \<open>d' division_of t \<inter> {u..v}\<close>
        proof -
          have \<open>{u..v} = cbox u v\<close> by (simp add: cbox_interval)
          then have \<open>{{u..v}} division_of {u..v}\<close>
            using \<open>{u..v} \<noteq> {}\<close> division_of_self by metis
          from division_inter[OF div this]
          have \<open>{k1 \<inter> k2 |k1 k2. k1 \<in> d \<and> k2 \<in> {{u..v}} \<and> k1 \<inter> k2 \<noteq> {}} division_of t \<inter> {u..v}\<close> .
          moreover have \<open>{k1 \<inter> k2 |k1 k2. k1 \<in> d \<and> k2 \<in> {{u..v}} \<and> k1 \<inter> k2 \<noteq> {}} = d'\<close>
            unfolding d'_def by auto
          ultimately show ?thesis by simp
        qed

        moreover have \<open>t \<inter> {u..v} \<subseteq> s\<close>
          using sub by auto
        moreover have \<open>sum content d' < r\<close>
        proof -
          have content_bound: \<open>sum content d' \<le> content (cbox u v)\<close>
            using subadditive_content_division[OF \<open>d' division_of t \<inter> {u..v}\<close>] by auto
          obtain x where \<open>(x, {u..v}) \<in> p\<close>
            using \<open>{u..v} \<in> D\<close> unfolding D_def by auto
          then have \<open>{u..v} \<subseteq> ball x \<delta>\<close>
            using fineD[OF p_fine] by auto
          then have uv_in: \<open>u \<in> ball x \<delta>\<close> \<open>v \<in> ball x \<delta>\<close>
            using \<open>{u..v} \<noteq> {}\<close> by auto
          have \<open>u \<le> v\<close> using \<open>{u..v} \<noteq> {}\<close> by auto
          have \<open>content (cbox u v) < r\<close>
          proof -
            from uv_in have \<open>dist x u < \<delta>\<close> \<open>dist x v < \<delta>\<close> by auto
            then have \<open>v - u < 2 * \<delta>\<close>
              by (auto simp: dist_real_def)
            also have \<open>\<dots> \<le> 2 * (r / 3)\<close>
              unfolding \<delta>_def by (auto simp: min_def)
            also have \<open>\<dots> < r\<close> using r_pos by auto
            finally show ?thesis
              using \<open>u \<le> v\<close> by (simp add: cbox_interval content_real)
          qed
          then show ?thesis using content_bound by linarith
        qed
        ultimately
        have \<open>(\<Sum>k\<in>d'. norm (f k)) < 1\<close>
          using r_bound by presburger
        show "(\<Sum>k\<in>d. norm (f (k \<inter> l))) \<le> 1"
        proof -
          have f_empty: \<open>f {} = 0\<close> using operative.empty[OF assms(1)] .
          have fin_d: \<open>finite d\<close> using division_ofD(1)[OF div] .
          have zero_terms: \<open>\<forall>k\<in>d. k \<inter> {u..v} = {} \<longrightarrow> norm (f (k \<inter> {u..v})) = 0\<close>
            by (simp add: f_empty)
          have \<open>(\<Sum>k\<in>d. norm (f (k \<inter> l))) = (\<Sum>k\<in>d. norm (f (k \<inter> {u..v})))\<close>
            by (simp add: luv)
          also have \<open>\<dots> = (\<Sum>k\<in>{k\<in>d. k \<inter> {u..v} \<noteq> {}}. norm (f (k \<inter> {u..v})))\<close>
          proof -
            have \<open>(\<Sum>k\<in>d. norm (f (k \<inter> {u..v})))
                 = (\<Sum>k\<in>{k\<in>d. k \<inter> {u..v} \<noteq> {}}. norm (f (k \<inter> {u..v})))
                 + (\<Sum>k\<in>{k\<in>d. k \<inter> {u..v} = {}}. norm (f (k \<inter> {u..v})))\<close>
              by (subst sum.union_disjoint[symmetric]) (auto intro: sum.cong simp: fin_d)
            also have \<open>(\<Sum>k\<in>{k\<in>d. k \<inter> {u..v} = {}}. norm (f (k \<inter> {u..v}))) = 0\<close>
              by (auto simp: f_empty)
            finally show ?thesis by simp
          qed
          also have \<open>\<dots> \<le> (\<Sum>k\<in>d'. norm (f k))\<close>
          proof -
            have fin_A: \<open>finite {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close> using fin_d by auto
            have collision: \<open>norm (f (k1 \<inter> {u..v})) = 0\<close>
              if k1_in: \<open>k1 \<in> {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close>
                and k2_in: \<open>k2 \<in> {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close>
                and neq: \<open>k1 \<noteq> k2\<close>
                and coll: \<open>k1 \<inter> {u..v} = k2 \<inter> {u..v}\<close>
              for k1 k2
            proof -
              have k1d: \<open>k1 \<in> d\<close> and k2d: \<open>k2 \<in> d\<close> using k1_in k2_in by auto
              have eq1: \<open>interior (k1 \<inter> {u..v}) = interior k1 \<inter> interior {u..v}\<close>
                by (rule interior_Int)
              have eq2: \<open>interior (k2 \<inter> {u..v}) = interior k2 \<inter> interior {u..v}\<close>
                by (rule interior_Int)
              have \<open>interior (k1 \<inter> {u..v}) = interior (k2 \<inter> {u..v})\<close>
                using coll by simp
              then have \<open>interior k1 \<inter> interior {u..v} = interior k2 \<inter> interior {u..v}\<close>
                using eq1 eq2 by simp
              then have sub: \<open>interior (k1 \<inter> {u..v}) \<subseteq> interior k1 \<inter> interior k2\<close>
                using eq1 by auto
              then have \<open>interior (k1 \<inter> {u..v}) = {}\<close>
                using division_ofD(5)[OF div k1d k2d neq] by auto
              obtain a1 b1 where k1_eq: \<open>k1 = cbox a1 b1\<close>
                using division_ofD(4)[OF div k1d] by auto
              have k1_uv: \<open>k1 \<inter> {u..v} = cbox (max a1 u) (min b1 v)\<close>
                by (simp add: k1_eq cbox_interval Int_atLeastAtMost)
              then have \<open>box (max a1 u) (min b1 v) = {}\<close>
                using \<open>interior (k1 \<inter> {u..v}) = {}\<close> by (simp add: interior_cbox)
              then have \<open>f (k1 \<inter> {u..v}) = 0\<close>
                using operative.box_empty_imp[OF assms(1)] k1_uv by auto
              then show ?thesis by simp
            qed

            have eq: \<open>(\<Sum>k\<in>d'. norm (f k))
                = (\<Sum>k\<in>{k \<in> d. k \<inter> {u..v} \<noteq> {}}. norm (f (k \<inter> {u..v})))\<close>
            proof -
              have \<open>sum (\<lambda>k. norm (f k)) ((\<lambda>k. k \<inter> {u..v}) ` {k \<in> d. k \<inter> {u..v} \<noteq> {}})
                  = sum ((\<lambda>k. norm (f k)) \<circ> (\<lambda>k. k \<inter> {u..v})) {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close>
              proof (intro sum.reindex_nontrivial[OF fin_A])
                fix x y
                assume \<open>x \<in> {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close> \<open>y \<in> {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close>
                  \<open>x \<noteq> y\<close> \<open>x \<inter> {u..v} = y \<inter> {u..v}\<close>
                then show \<open>norm (f (x \<inter> {u..v})) = 0\<close>
                  using collision by auto
              qed
              then show ?thesis unfolding d'_def comp_def by auto
            qed
            then show ?thesis by simp
          qed
          also have \<open>\<dots> < 1\<close> using \<open>(\<Sum>k\<in>d'. norm (f k)) < 1\<close> .
          finally show ?thesis by simp
        qed
      qed
      then show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  then show ?thesis
    using has_bounded_setvariation_on_def by blast
qed

section \<open>Absolute continuity for functions\<close>

definition absolutely_continuous_on ::
  "(real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> real set \<Rightarrow> bool" where
  "absolutely_continuous_on f s \<longleftrightarrow>
    absolutely_setcontinuous_on (\<lambda>k. f (Sup k) - f (Inf k)) s"

subsection \<open>Basic properties\<close>

lemma absolutely_continuous_on_eq:
  "\<lbrakk>\<And>x. x \<in> s \<Longrightarrow> f x = g x; absolutely_continuous_on f s\<rbrakk> \<Longrightarrow>
    absolutely_continuous_on g s"
proof -
  assume eq: "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
    and ac: "absolutely_continuous_on f s"
  have "\<And>k. k \<in> d \<Longrightarrow> d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow> g (Sup k) - g (Inf k) = f (Sup k) - f (Inf k)"
    for d t
  proof -
    fix k assume "k \<in> d" "d division_of t" "t \<subseteq> s"
    then obtain a b where kb: "k = cbox a b" and "k \<subseteq> t"
      using division_ofD(4) division_ofD(2) by meson
    moreover have "k \<noteq> {}" using \<open>k \<in> d\<close> \<open>d division_of t\<close> division_ofD(3) by blast
    ultimately have "a \<le> b" using kb by auto
    then have "a \<in> s" "b \<in> s"
      using \<open>k \<subseteq> t\<close> \<open>t \<subseteq> s\<close> kb by auto
    then show "g (Sup k) - g (Inf k) = f (Sup k) - f (Inf k)"
      using eq kb \<open>a \<le> b\<close> by auto
  qed
  then show ?thesis
    using ac unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
    by (metis (no_types, lifting) sum.cong)
qed

lemma absolutely_continuous_on_subset:
  "absolutely_continuous_on f s \<Longrightarrow> t \<subseteq> s \<Longrightarrow> absolutely_continuous_on f t"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  by (meson order_trans)

lemma absolutely_continuous_on_const:
  "absolutely_continuous_on (\<lambda>x. c) s"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  by simp

lemma absolutely_continuous_on_cmul:
  "absolutely_continuous_on f s \<Longrightarrow> absolutely_continuous_on (\<lambda>x. a *\<^sub>R f x) s"
proof (cases "a = 0")
  case True then show ?thesis
    by (simp add: absolutely_continuous_on_const)
next
  case False
  assume ac: "absolutely_continuous_on f s"
  show ?thesis
    unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    then have "\<epsilon> / \<bar>a\<bar> > 0" using False by simp
    then obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
      (\<Sum>k\<in>d. content k) < \<delta> \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / \<bar>a\<bar>"
      using ac unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
      by (meson order.strict_trans2)
    show "\<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm (a *\<^sub>R f (Sup k) - a *\<^sub>R f (Inf k))) < \<epsilon>"
    proof (intro exI conjI allI impI)
      show "\<delta> > 0" by fact
    next
      fix d t assume H: "d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta>"
      then have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / \<bar>a\<bar>"
        using \<delta> by auto
      then have "\<bar>a\<bar> * (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
        using False by (simp add: field_simps)
      moreover have "(\<Sum>k\<in>d. norm (a *\<^sub>R f (Sup k) - a *\<^sub>R f (Inf k))) =
        \<bar>a\<bar> * (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))" 
        by (simp add: scaleR_diff_right[symmetric] norm_scaleR sum_distrib_left)
      ultimately show "(\<Sum>k\<in>d. norm (a *\<^sub>R f (Sup k) - a *\<^sub>R f (Inf k))) < \<epsilon>"
        by linarith
    qed
  qed
qed

lemma absolutely_continuous_on_neg:
  "absolutely_continuous_on f s \<Longrightarrow> absolutely_continuous_on (\<lambda>x. - f x) s"
  using absolutely_continuous_on_cmul[of f s "-1"] by simp

lemma absolutely_continuous_on_add:
  "absolutely_continuous_on f s \<Longrightarrow> absolutely_continuous_on g s \<Longrightarrow>
    absolutely_continuous_on (\<lambda>x. f x + g x) s"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
proof (intro allI impI)
  fix \<epsilon> :: real assume "\<epsilon> > 0"
  assume acf: "\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
  assume acg: "\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
    (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) < \<epsilon>"
  obtain \<delta>1 where "\<delta>1 > 0" and \<delta>1: "\<forall>d t. d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta>1 \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>/2"
    using acf \<open>\<epsilon> > 0\<close> by (auto dest: spec[of _ "\<epsilon>/2"])
  obtain \<delta>2 where "\<delta>2 > 0" and \<delta>2: "\<forall>d t. d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta>2 \<longrightarrow>
    (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) < \<epsilon>/2"
    using acg \<open>\<epsilon> > 0\<close> by (auto dest: spec[of _ "\<epsilon>/2"])
  show "\<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) + g (Sup k) - (f (Inf k) + g (Inf k)))) < \<epsilon>"
  proof (intro exI conjI allI impI)
    show "min \<delta>1 \<delta>2 > 0" using \<open>\<delta>1 > 0\<close> \<open>\<delta>2 > 0\<close> by auto
  next
    fix d t assume H: "d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < min \<delta>1 \<delta>2"
    have f_bd: "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>/2" using \<delta>1 H by auto
    have g_bd: "(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) < \<epsilon>/2" using \<delta>2 H by auto
    have "(\<Sum>k\<in>d. norm (f (Sup k) + g (Sup k) - (f (Inf k) + g (Inf k)))) \<le>
      (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) + norm (g (Sup k) - g (Inf k)))"
      by (intro sum_mono norm_diff_triangle_ineq)
    also have "\<dots> = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) + (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
      by (rule sum.distrib)
    also have "\<dots> < \<epsilon>" using f_bd g_bd by linarith
    finally show "(\<Sum>k\<in>d. norm (f (Sup k) + g (Sup k) - (f (Inf k) + g (Inf k)))) < \<epsilon>" .
  qed
qed

lemma absolutely_continuous_on_sub:
  "absolutely_continuous_on f s \<Longrightarrow> absolutely_continuous_on g s \<Longrightarrow>
    absolutely_continuous_on (\<lambda>x. f x - g x) s"
  using absolutely_continuous_on_add[of f s "\<lambda>x. - g x"] absolutely_continuous_on_neg by auto

lemma absolutely_continuous_on_norm:
  "absolutely_continuous_on f s \<Longrightarrow>
    absolutely_continuous_on (\<lambda>x. norm (f x) *\<^sub>R e) s"
proof (cases "e = 0")
  case True then show ?thesis by (simp add: absolutely_continuous_on_const)
next
  case False
  assume ac: "absolutely_continuous_on f s"
  show ?thesis
    unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    then have "\<epsilon> / norm e > 0" using False by simp
    then obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
      (\<Sum>k\<in>d. content k) < \<delta> \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / norm e"
      using ac unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
      by (meson order.strict_trans2)
    show "\<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm (norm (f (Sup k)) *\<^sub>R e - norm (f (Inf k)) *\<^sub>R e)) < \<epsilon>"
    proof (intro exI conjI allI impI)
      show "\<delta> > 0" by fact
    next
      fix d t assume H: "d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta>"
      have bd: "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / norm e"
        using \<delta> H by auto
      have "(\<Sum>k\<in>d. norm (norm (f (Sup k)) *\<^sub>R e - norm (f (Inf k)) *\<^sub>R e)) =
        (\<Sum>k\<in>d. \<bar>norm (f (Sup k)) - norm (f (Inf k))\<bar> * norm e)"
        by (simp add: scaleR_diff_left[symmetric] abs_real_def norm_scaleR)
      also have "\<dots> \<le> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) * norm e)"
        by (intro sum_mono mult_right_mono norm_triangle_ineq3) auto
      also have "\<dots> = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) * norm e"
        by (simp add: sum_distrib_right)
      also have "\<dots> < (\<epsilon> / norm e) * norm e"
        using bd False by (intro mult_strict_right_mono) auto
      also have "\<dots> = \<epsilon>" using False by simp
      finally show "(\<Sum>k\<in>d. norm (norm (f (Sup k)) *\<^sub>R e - norm (f (Inf k)) *\<^sub>R e)) < \<epsilon>" .
    qed
  qed
qed

lemma absolutely_continuous_on_compose_linear:
  "absolutely_continuous_on f s \<Longrightarrow> linear h \<Longrightarrow>
    absolutely_continuous_on (h \<circ> f) s"
proof -
  assume ac: "absolutely_continuous_on f s" and lin: "linear h"
  then obtain K where "K > 0" and K: "\<And>x. norm (h x) \<le> norm x * K"
    using linear_conv_bounded_linear bounded_linear.pos_bounded by blast
  show ?thesis
    unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def o_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    then have "\<epsilon> / K > 0" using \<open>K > 0\<close> by simp
    then obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
      (\<Sum>k\<in>d. content k) < \<delta> \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / K"
      using ac unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
      by (meson order.strict_trans2)
    show "\<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm (h (f (Sup k)) - h (f (Inf k)))) < \<epsilon>"
    proof (intro exI conjI allI impI)
      show "\<delta> > 0" by fact
    next
      fix d t assume H: "d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta>"
      have "(\<Sum>k\<in>d. norm (h (f (Sup k)) - h (f (Inf k)))) =
        (\<Sum>k\<in>d. norm (h (f (Sup k) - f (Inf k))))"
        using lin by (simp add: linear_diff)
      also have "\<dots> \<le> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) * K)"
        by (intro sum_mono K)
      also have "\<dots> = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) * K"
        by (simp add: sum_distrib_right)
      also have "\<dots> < (\<epsilon> / K) * K"
        using \<delta> H \<open>K > 0\<close> by (intro mult_strict_right_mono) auto
      also have "\<dots> = \<epsilon>" using \<open>K > 0\<close> by simp
      finally show "(\<Sum>k\<in>d. norm (h (f (Sup k)) - h (f (Inf k)))) < \<epsilon>" .
    qed
  qed
qed

lemma absolutely_continuous_on_null:
  "content {a..b} = 0 \<Longrightarrow> absolutely_continuous_on f {a..b}"
proof -
  assume cnt: "content {a..b} = 0"
  then have ba: "b \<le> a" using content_real_eq_0 by auto
  show ?thesis
    unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    show "\<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
    proof (intro exI conjI allI impI)
      show "(1::real) > 0" by simp
    next
      fix d t assume H: "d division_of t \<and> t \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < 1"
      then have div: "d division_of t" and sub: "t \<subseteq> {a..b}" by auto
      have "\<forall>k\<in>d. f (Sup k) - f (Inf k) = 0"
      proof
        fix k assume kd: "k \<in> d"
        then obtain u v where uv: "k = cbox u v" and kt: "k \<subseteq> t"
          using div division_ofD(4) division_ofD(2) by meson
        have kne: "k \<noteq> {}" using kd div division_ofD(3) by blast
        then have "u \<le> v" using uv by auto
        have "k \<subseteq> {a..b}" using kt sub by auto
        then have "u \<ge> a" "v \<le> b" using uv \<open>u \<le> v\<close> by auto
        then have "u = v" using ba \<open>u \<le> v\<close> by linarith
        then show "f (Sup k) - f (Inf k) = 0"
          using uv by simp
      qed
      then show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
        using \<open>\<epsilon> > 0\<close> by simp
    qed
  qed
qed
lemma absolutely_continuous_on_id:
  "absolutely_continuous_on id {a..b}"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
proof (intro allI impI)
  fix \<epsilon> :: real assume "\<epsilon> > 0"
  show "\<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
    (\<Sum>k\<in>d. norm (id (Sup k) - id (Inf k))) < \<epsilon>"
  proof (intro exI conjI allI impI)
    show "\<epsilon> > 0" by fact
  next
    fix d t assume H: "d division_of t \<and> t \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < \<epsilon>"
    then have div: "d division_of t" by auto
    have "(\<Sum>k\<in>d. norm (id (Sup k) - id (Inf k))) = (\<Sum>k\<in>d. content k)"
    proof (rule sum.cong, simp)
      fix k assume kd: "k \<in> d"
      then obtain u v where uv: "k = cbox u v" and kt: "k \<subseteq> t"
        using div division_ofD(4) division_ofD(2) by meson
      have "k \<noteq> {}" using kd div division_ofD(3) by blast
      then have le: "u \<le> v" using uv by auto
      then show "norm (id (Sup k) - id (Inf k)) = content k"
        using uv by (simp add: content_real)
    qed
    also have "\<dots> < \<epsilon>" using H by auto
    finally show "(\<Sum>k\<in>d. norm (id (Sup k) - id (Inf k))) < \<epsilon>" .
  qed
qed

subsection \<open>Relationship to bounded variation and continuity\<close>

lemma absolutely_continuous_on_imp_continuous:
  assumes "absolutely_continuous_on f s" "is_interval s"
  shows "continuous_on s f"
proof (rule continuous_on_iff[THEN iffD2], intro ballI allI impI)
  fix x \<epsilon> :: real assume xs: "x \<in> s" and "\<epsilon> > 0"
  then obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
    (\<Sum>k\<in>d. content k) < \<delta> \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
    using assms(1) unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
    by (meson order.strict_trans2)
  show "\<exists>\<delta>>0. \<forall>x'\<in>s. dist x' x < \<delta> \<longrightarrow> dist (f x') (f x) < \<epsilon>"
  proof (intro exI conjI ballI impI)
    show "\<delta> > 0" by fact
  next
    fix y assume ys: "y \<in> s" and dyx: "dist y x < \<delta>"
    show "dist (f y) (f x) < \<epsilon>"
    proof (cases "x = y")
      case True then show ?thesis using \<open>\<epsilon> > 0\<close> by simp
    next
      case False
      define lo hi where "lo = min x y" and "hi = max x y"
      then have lohi: "lo \<le> hi" and lox: "lo \<le> x" and hix: "x \<le> hi"
        and loy: "lo \<le> y" and hiy: "y \<le> hi"
        by (auto simp: min_def max_def)
      have sub: "{lo..hi} \<subseteq> s"
      proof
        fix z assume "z \<in> {lo..hi}"
        then have "lo \<le> z" "z \<le> hi" by auto
        show "z \<in> s"
          using assms(2) xs ys \<open>lo \<le> z\<close> \<open>z \<le> hi\<close>
          unfolding lo_def hi_def is_interval_1
          by (metis (full_types) le_cases min_def max_def order_trans)
      qed
      have ne: "cbox lo hi \<noteq> {}" using lohi by auto
      have div: "{cbox lo hi} division_of cbox lo hi"
        by (rule division_of_self[OF ne])
      have "(\<Sum>k\<in>{cbox lo hi}. content k) = content {lo..hi}" by simp
      also have "\<dots> = hi - lo" using content_real lohi by auto
      also have "\<dots> = dist y x"
        unfolding lo_def hi_def dist_real_def by (auto simp: min_def max_def)
      also have "\<dots> < \<delta>" by fact
      finally have sm: "(\<Sum>k\<in>{cbox lo hi}. content k) < \<delta>" .
      have "(\<Sum>k\<in>{cbox lo hi}. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
        using \<delta>[OF div] sub sm by auto
      then have "norm (f hi - f lo) < \<epsilon>" using lohi by simp
      then show "dist (f y) (f x) < \<epsilon>"
      proof (cases "x \<le> y")
        case True then show ?thesis
          using \<open>norm (f hi - f lo) < \<epsilon>\<close> lo_def hi_def by (simp add: dist_norm norm_minus_commute)
      next
        case False then show ?thesis
          using \<open>norm (f hi - f lo) < \<epsilon>\<close> lo_def hi_def by (simp add: dist_norm norm_minus_commute)
      qed
    qed
  qed
qed

lemma absolutely_continuous_on_imp_has_bounded_variation_on:
  "absolutely_continuous_on f {a..b} \<Longrightarrow> has_bounded_variation_on f {a..b}"
  unfolding absolutely_continuous_on_def has_bounded_variation_on_def
proof -
  assume ac: \<open>absolutely_setcontinuous_on (\<lambda>k. f (Sup k) - f (Inf k)) {a..b}\<close>
  show \<open>has_bounded_setvariation_on (\<lambda>k. f (Sup k) - f (Inf k)) {a..b}\<close>
    sorry
qed

lemma Lipschitz_imp_absolutely_continuous:
  assumes "\<And>x y. x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> norm (f x - f y) \<le> B * \<bar>x - y\<bar>"
  shows "absolutely_continuous_on f s"
  sorry

subsection \<open>Combining intervals\<close>

lemma absolutely_continuous_on_combine:
  assumes acL: "absolutely_continuous_on f {a..c}"
    and acR: "absolutely_continuous_on f {c..b}" and "a \<le> c" "c \<le> b"
  shows "absolutely_continuous_on f {a..b}"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
proof (intro allI impI)
  fix \<epsilon> :: real assume "\<epsilon> > 0"
  then obtain \<delta>1 where "\<delta>1 > 0" and \<delta>1: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> {a..c} \<Longrightarrow>
    (\<Sum>k\<in>d. content k) < \<delta>1 \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>/2"
    using acL unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
    by (meson half_gt_zero order.strict_trans2)
  obtain \<delta>2 where "\<delta>2 > 0" and \<delta>2: "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> {c..b} \<Longrightarrow>
    (\<Sum>k\<in>d. content k) < \<delta>2 \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>/2"
    using acR \<open>\<epsilon> > 0\<close> unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
    by (meson half_gt_zero order.strict_trans2)
  define \<delta> where "\<delta> = min \<delta>1 \<delta>2"
  show "\<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
  proof (intro exI conjI allI impI)
    show "\<delta> > 0" using \<open>\<delta>1 > 0\<close> \<open>\<delta>2 > 0\<close> \<delta>_def by auto
  next
    fix d t assume H: "d division_of t \<and> t \<subseteq> {a..b} \<and> (\<Sum>k\<in>d. content k) < \<delta>"
    then have div: "d division_of t" and sub: "t \<subseteq> {a..b}" 
      and sm: "(\<Sum>k\<in>d. content k) < \<delta>" by auto
    have fin: "finite d" using div by auto
    \<comment> \<open>Split d into left and right parts at c using division_inter\<close>
    define dL where "dL = {k \<inter> {a..c} | k. k \<in> d \<and> k \<inter> {a..c} \<noteq> {}}"
    define dR where "dR = {k \<inter> {c..b} | k. k \<in> d \<and> k \<inter> {c..b} \<noteq> {}}"
    have ne_ac: "cbox a c \<noteq> {}" using \<open>a \<le> c\<close> by auto
    have ne_cb: "cbox c b \<noteq> {}" using \<open>c \<le> b\<close> by auto
    have div_ac: "{cbox a c} division_of cbox a c" using division_of_self[OF ne_ac] .
    have div_cb: "{cbox c b} division_of cbox c b" using division_of_self[OF ne_cb] .
    have dL_eq: "dL = {k1 \<inter> k2 |k1 k2. k1 \<in> d \<and> k2 \<in> {{a..c}} \<and> k1 \<inter> k2 \<noteq> {}}"
      unfolding dL_def by auto
    have dR_eq: "dR = {k1 \<inter> k2 |k1 k2. k1 \<in> d \<and> k2 \<in> {{c..b}} \<and> k1 \<inter> k2 \<noteq> {}}"
      unfolding dR_def by auto
    have dL_div: "dL division_of (t \<inter> {a..c})"
      unfolding dL_eq using division_inter[OF div div_ac[unfolded box_real]] by auto
    have dR_div: "dR division_of (t \<inter> {c..b})"
      unfolding dR_eq using division_inter[OF div div_cb[unfolded box_real]] by auto
    have dL_sub: "t \<inter> {a..c} \<subseteq> {a..c}" by auto
    have dR_sub: "t \<inter> {c..b} \<subseteq> {c..b}" by auto
    \<comment> \<open>Content sums: each part has content \<le> total\<close>
    have content_L: "(\<Sum>k\<in>dL. content k) \<le> (\<Sum>k\<in>d. content k)"
    proof (rule sum_le_included[where i="\<lambda>k. k \<inter> {a..c}"])
      show "finite dL" using dL_div by auto
    next
      show "finite d" using fin .
    next
      show "\<forall>y\<in>d. 0 \<le> content y" by (simp add: content_pos_le)
    next
      show "\<forall>x\<in>dL. \<exists>y\<in>d. y \<inter> {a..c} = x \<and> content x \<le> content y"
      proof
        fix x assume "x \<in> dL"
        then obtain k where kd: "k \<in> d" and kne: "k \<inter> {a..c} \<noteq> {}" and xeq: "x = k \<inter> {a..c}"
          unfolding dL_def by auto
        have "k \<subseteq> t" using div division_ofD(2) kd by blast
        then have "k \<subseteq> {a..b}" using sub by auto
        obtain u v where kuv: "k = cbox u v" using div division_ofD(4) kd by meson
        have kcbox: "k \<inter> {a..c} = cbox (max u a) (min v c)"
          using kuv by (simp add: box_real Int_interval)
        have "cbox (max u a) (min v c) \<subseteq> cbox u v" by auto
        then have "content (k \<inter> {a..c}) \<le> content k"
          by (metis content_subset kcbox kuv)
        then show "\<exists>y\<in>d. y \<inter> {a..c} = x \<and> content x \<le> content y"
          using kd xeq by auto
      qed
    qed

    have content_R: "(\<Sum>k\<in>dR. content k) \<le> (\<Sum>k\<in>d. content k)"
    proof (rule sum_le_included[where i="\<lambda>k. k \<inter> {c..b}"])
      show "finite dR" using dR_div by auto
    next
      show "finite d" using fin .
    next
      show "\<forall>y\<in>d. 0 \<le> content y" by (simp add: content_pos_le)
    next
      show "\<forall>x\<in>dR. \<exists>y\<in>d. y \<inter> {c..b} = x \<and> content x \<le> content y"
      proof
        fix x assume "x \<in> dR"
        then obtain k where kd: "k \<in> d" and xeq: "x = k \<inter> {c..b}"
          unfolding dR_def by auto
        obtain u v where kuv: "k = cbox u v" using div division_ofD(4) kd by meson
        have kcbox: "k \<inter> {c..b} = cbox (max u c) (min v b)"
          using kuv by (simp add: box_real Int_interval)
        have "cbox (max u c) (min v b) \<subseteq> cbox u v" by auto
        then have "content (k \<inter> {c..b}) \<le> content k"
          by (metis content_subset kcbox kuv)
        then show "\<exists>y\<in>d. y \<inter> {c..b} = x \<and> content x \<le> content y"
          using kd xeq by auto
      qed
    qed
    \<comment> \<open>Norm sums: triangle inequality at the split point\<close>
    have norm_split: "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) 
      \<le> (\<Sum>k\<in>dL. norm (f (Sup k) - f (Inf k))) + (\<Sum>k\<in>dR. norm (f (Sup k) - f (Inf k)))"
      sorry
    have "(\<Sum>k\<in>dL. content k) < \<delta>1"
      using content_L sm \<delta>_def by linarith
    then have L_bd: "(\<Sum>k\<in>dL. norm (f (Sup k) - f (Inf k))) < \<epsilon>/2"
      using \<delta>1[OF dL_div dL_sub] by auto
    have "(\<Sum>k\<in>dR. content k) < \<delta>2"
      using content_R sm \<delta>_def by linarith
    then have R_bd: "(\<Sum>k\<in>dR. norm (f (Sup k) - f (Inf k))) < \<epsilon>/2"
      using \<delta>2[OF dR_div dR_sub] by auto
    show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
      using norm_split L_bd R_bd by linarith
  qed
qed

lemma absolutely_continuous_on_division:
  assumes "\<And>k. k \<in> d \<Longrightarrow> absolutely_continuous_on f k"
    "d division_of {a..b}"
  shows "absolutely_continuous_on f {a..b}"
  sorry

subsection \<open>Bilinear and product\<close>

lemma absolutely_continuous_on_bilinear:
  assumes "absolutely_continuous_on f {a..b}"
    "absolutely_continuous_on g {a..b}" "bounded_bilinear h"
  shows "absolutely_continuous_on (\<lambda>x. h (f x) (g x)) {a..b}"
  sorry

lemma absolutely_continuous_on_mul:
  assumes "absolutely_continuous_on f {a..b}"
    "absolutely_continuous_on g {a..b}"
  shows "absolutely_continuous_on (\<lambda>x. f x * g x) {a..(b::real)}"
  sorry

subsection \<open>Fundamental theorem of calculus\<close>

theorem fundamental_theorem_of_calculus_absolutely_continuous:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "negligible S" "a \<le> b"
    "absolutely_continuous_on f {a..b}"
    "\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})"
  shows "(f' has_integral (f b - f a)) {a..b}"
  sorry

subsection \<open>Closure and interior\<close>

lemma absolutely_continuous_on_closure:
  assumes "absolutely_continuous_on f (interior {a..b})"
    "continuous_on {a..b} f"
  shows "absolutely_continuous_on f {a..b}"
  sorry

end
