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
  "('a::euclidean_space set \<Rightarrow> 'b::euclidean_space) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "absolutely_setcontinuous_on f s \<longleftrightarrow>
    (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> s \<and>
      (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow> (\<Sum>k\<in>d. norm (f k)) < \<epsilon>)"

lemma absolutely_setcontinuous_on_subset:
  assumes \<open>absolutely_setcontinuous_on f s\<close> \<open>t \<subseteq> s\<close>
  shows \<open>absolutely_setcontinuous_on f t\<close>
  using assms unfolding absolutely_setcontinuous_on_def by (meson order_trans)

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
          have collision: \<open>norm (f (k1 \<inter> {u..v})) = 0\<close>
            if k1d: \<open>k1 \<in> d\<close> and k2d: \<open>k2 \<in> d\<close> and neq: \<open>k1 \<noteq> k2\<close>
              and coll: \<open>k1 \<inter> {u..v} = k2 \<inter> {u..v}\<close>
            for k1 k2
          proof -
            have \<open>interior k1 \<inter> interior {u..v} = interior k2 \<inter> interior {u..v}\<close>
              using arg_cong[OF coll, of interior] by (simp add: interior_Int)
            then have \<open>interior (k1 \<inter> {u..v}) \<subseteq> interior k1 \<inter> interior k2\<close>
              by (auto simp: interior_Int)
            then have \<open>interior (k1 \<inter> {u..v}) = {}\<close>
              using division_ofD(5)[OF div k1d k2d neq] by auto
            obtain a1 b1 where k1_eq: \<open>k1 = cbox a1 b1\<close>
              using division_ofD(4)[OF div k1d] by blast
            have k1_uv: \<open>k1 \<inter> {u..v} = cbox (max a1 u) (min b1 v)\<close>
              by (simp add: k1_eq cbox_interval Int_atLeastAtMost)
            then have \<open>box (max a1 u) (min b1 v) = {}\<close>
              using \<open>interior (k1 \<inter> {u..v}) = {}\<close> by (simp add: interior_cbox)
            then show ?thesis
              using operative.box_empty_imp[OF assms(1)] k1_uv by auto
          qed
          \<comment> \<open>Reindex via SUM_IMAGE_NONZERO\<close>
          have fin_A: \<open>finite {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close> using fin_d by auto
          have reindex: \<open>sum (\<lambda>k. norm (f k)) ((\<lambda>k. k \<inter> {u..v}) ` {k \<in> d. k \<inter> {u..v} \<noteq> {}})
              = sum ((\<lambda>k. norm (f k)) \<circ> (\<lambda>k. k \<inter> {u..v})) {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close>
          proof (intro sum.reindex_nontrivial[OF fin_A])
            fix x y
            assume \<open>x \<in> {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close> \<open>y \<in> {k \<in> d. k \<inter> {u..v} \<noteq> {}}\<close>
              \<open>x \<noteq> y\<close> \<open>x \<inter> {u..v} = y \<inter> {u..v}\<close>
            then show \<open>norm (f (x \<inter> {u..v})) = 0\<close>
              using collision by auto
          qed
          have \<open>(\<Sum>k\<in>d. norm (f (k \<inter> l)))
              = (\<Sum>k\<in>{k \<in> d. k \<inter> {u..v} \<noteq> {}}. norm (f (k \<inter> {u..v})))\<close>
            by (auto intro!: sum.mono_neutral_right simp: luv f_empty fin_d)
          also have \<open>\<dots> = (\<Sum>k\<in>d'. norm (f k))\<close>
            using reindex unfolding d'_def comp_def by auto
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
  "real set \<Rightarrow> (real \<Rightarrow> 'a::euclidean_space) \<Rightarrow> bool" where
  "absolutely_continuous_on s f \<longleftrightarrow>
    absolutely_setcontinuous_on (\<lambda>k. f (Sup k) - f (Inf k)) s"

subsection \<open>Basic properties\<close>

lemma absolutely_continuous_on_eq:
  "\<lbrakk>\<And>x. x \<in> s \<Longrightarrow> f x = g x; absolutely_continuous_on s f\<rbrakk> \<Longrightarrow>
    absolutely_continuous_on s g"
proof -
  assume eq: "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
    and ac: "absolutely_continuous_on s f"
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
  "absolutely_continuous_on s f \<Longrightarrow> t \<subseteq> s \<Longrightarrow> absolutely_continuous_on t f"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  by (meson order_trans)

lemma absolutely_continuous_on_const:
  "absolutely_continuous_on s (\<lambda>x. c)"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  by simp

lemma absolutely_continuous_on_cmul:
  "absolutely_continuous_on s f \<Longrightarrow> absolutely_continuous_on s (\<lambda>x. a *\<^sub>R f x)"
proof (cases "a = 0")
  case True then show ?thesis
    by (simp add: absolutely_continuous_on_const)
next
  case False
  assume ac: "absolutely_continuous_on s f"
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
  "absolutely_continuous_on s f \<Longrightarrow> absolutely_continuous_on s (\<lambda>x. - f x)"
  using absolutely_continuous_on_cmul[of s f "-1"] by simp

lemma absolutely_continuous_on_add:
  "absolutely_continuous_on s f \<Longrightarrow> absolutely_continuous_on s g \<Longrightarrow>
    absolutely_continuous_on s (\<lambda>x. f x + g x)"
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
  "absolutely_continuous_on s f \<Longrightarrow> absolutely_continuous_on s g \<Longrightarrow>
    absolutely_continuous_on s (\<lambda>x. f x - g x)"
  using absolutely_continuous_on_add[of s f "\<lambda>x. - g x"] absolutely_continuous_on_neg by auto

lemma absolutely_continuous_on_norm:
  "absolutely_continuous_on s f \<Longrightarrow>
    absolutely_continuous_on s (\<lambda>x. norm (f x) *\<^sub>R e)"
proof (cases "e = 0")
  case True then show ?thesis by (simp add: absolutely_continuous_on_const)
next
  case False
  assume ac: "absolutely_continuous_on s f"
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
  "absolutely_continuous_on s f \<Longrightarrow> linear h \<Longrightarrow>
    absolutely_continuous_on s (h \<circ> f)"
proof -
  assume ac: "absolutely_continuous_on s f" and lin: "linear h"
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
  "content {a..b} = 0 \<Longrightarrow> absolutely_continuous_on {a..b} f"
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
  "absolutely_continuous_on {a..b} id"
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
  assumes "absolutely_continuous_on s f" "is_interval s"
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
        using \<open>norm (f hi - f lo) < \<epsilon>\<close> lo_def hi_def 
        by (cases "x \<le> y") (auto simp: dist_norm norm_minus_commute)
    qed
  qed
qed

lemma operative_function_endpoint_diff:
  fixes f :: \<open>real \<Rightarrow> 'a::real_normed_vector\<close>
  defines \<open>h \<equiv> \<lambda>S. if S = {} then 0 else f (Sup S) - f (Inf S)\<close>
  shows \<open>operative (+) 0 h\<close>
proof (rule operative.intro)
  show \<open>comm_monoid_set (+) (0::'a)\<close>
    using sum.comm_monoid_set_axioms .
next
  show \<open>operative_axioms (+) 0 h\<close>
  proof (rule operative_axioms.intro)
    fix a b :: real
    assume \<open>box a b = {}\<close>
    then have \<open>a \<ge> b\<close> by (simp add: box_eq_empty)
    then show \<open>h (cbox a b) = 0\<close>
      by (cases \<open>a = b\<close>) (auto simp: h_def cbox_interval)
  next
    fix a b c :: real and k :: real
    assume \<open>k \<in> Basis\<close>
    then have k1: \<open>k = 1\<close> by (simp add: Basis_real_def)
    have eq1: \<open>cbox a b \<inter> {x. x \<bullet> k \<le> c} = {a..min b c}\<close> if \<open>a \<le> b\<close> for c
      using k1 that by (auto simp: cbox_interval min_def)
    have eq2: \<open>cbox a b \<inter> {x. c \<le> x \<bullet> k} = {max a c..b}\<close> if \<open>a \<le> b\<close> for c
      using k1 that by (auto simp: cbox_interval max_def)
    show \<open>h (cbox a b) = h (cbox a b \<inter> {x. x \<bullet> k \<le> c}) + h (cbox a b \<inter> {x. c \<le> x \<bullet> k})\<close>
    proof (cases \<open>a \<le> b\<close>)
      case True
      then show ?thesis
        using eq1[OF True] eq2[OF True]
        by (cases \<open>c < a\<close>; cases \<open>b < c\<close>) (auto simp: h_def cbox_interval min_def max_def)
    next
      case False
      then have \<open>cbox a b = {}\<close> by (auto simp: cbox_interval)
      then show ?thesis by (simp add: h_def)
    qed
  qed
qed

lemma operative_absolutely_setcontinuous_on:
  fixes g :: \<open>'a::euclidean_space set \<Rightarrow> 'b::euclidean_space\<close>
  assumes \<open>operative (+) 0 g\<close>
  shows \<open>operative (\<and>) True (absolutely_setcontinuous_on g)\<close>
proof -
  note null = operative.box_empty_imp[OF assms]
  note split = operative.Basis_imp[OF assms, symmetric]
  show ?thesis
  proof (intro operative.intro comm_monoid_set_and operative_axioms.intro iffI)
    show \<open>absolutely_setcontinuous_on g (cbox a b)\<close> if \<open>box a b = {}\<close> for a b
    proof -
      have \<open>g k = 0\<close> if kd: \<open>k \<in> d\<close> and div: \<open>d division_of t\<close> and sub: \<open>t \<subseteq> cbox a b\<close> for k d t
      proof -
        obtain a' b' where kab: \<open>k = cbox a' b'\<close> using division_ofD(4)[OF div kd] by auto
        have \<open>box a' b' = {}\<close>
          using division_ofD(2)[OF div kd] sub \<open>box a b = {}\<close>
          by (metis bot.extremum_uniqueI interior_cbox interior_mono kab)
        then show ?thesis using null kab by auto
      qed
      then show ?thesis using that
        unfolding absolutely_setcontinuous_on_def
        by (intro iffI TrueI allI impI exI[of _ 1]) (auto simp: division_ofD(1))
    qed
  next
    fix a b c and k::'a
    assume \<open>k \<in> Basis\<close>
    assume \<open>absolutely_setcontinuous_on g (cbox a b \<inter> {x. x \<bullet> k \<le> c}) \<and>
            absolutely_setcontinuous_on g (cbox a b \<inter> {x. c \<le> x \<bullet> k})\<close>
    then obtain acL acR
      where acL: \<open>absolutely_setcontinuous_on g (cbox a b \<inter> {x. x \<bullet> k \<le> c})\<close>
        and acR: \<open>absolutely_setcontinuous_on g (cbox a b \<inter> {x. c \<le> x \<bullet> k})\<close>
      by auto
    show \<open>absolutely_setcontinuous_on g (cbox a b)\<close>
      unfolding absolutely_setcontinuous_on_def
    proof (intro allI impI)
      fix e :: real assume \<open>e > 0\<close>
      then have e2: \<open>e / 2 > 0\<close> by simp
      from acL[unfolded absolutely_setcontinuous_on_def, rule_format, OF e2]
      obtain r1 where r1: \<open>r1 > 0\<close>
        and L: \<open>\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> cbox a b \<inter> {x. x \<bullet> k \<le> c} \<Longrightarrow>
          (\<Sum>k\<in>d. content k) < r1 \<Longrightarrow> (\<Sum>k\<in>d. norm (g k)) < e / 2\<close>
        by (auto simp: imp_conjL)
      from acR[unfolded absolutely_setcontinuous_on_def, rule_format, OF e2]
      obtain r2 where r2: \<open>r2 > 0\<close>
        and R: \<open>\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> cbox a b \<inter> {x. c \<le> x \<bullet> k} \<Longrightarrow>
          (\<Sum>k\<in>d. content k) < r2 \<Longrightarrow> (\<Sum>k\<in>d. norm (g k)) < e / 2\<close>
        by (auto simp: imp_conjL)
      show \<open>\<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> cbox a b \<and>
        (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow> (\<Sum>k\<in>d. norm (g k)) < e\<close>
      proof (intro exI[of _ \<open>min r1 r2\<close>] conjI allI impI)
        show \<open>min r1 r2 > 0\<close> using r1 r2 by simp
      next
        fix d t
        assume H: \<open>d division_of t \<and> t \<subseteq> cbox a b \<and> (\<Sum>k\<in>d. content k) < min r1 r2\<close>
        then have div: \<open>d division_of t\<close> and sub: \<open>t \<subseteq> cbox a b\<close>
          and content_bound: \<open>(\<Sum>k\<in>d. content k) < r1\<close> \<open>(\<Sum>k\<in>d. content k) < r2\<close>
          by auto
        define dL where \<open>dL = (\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c}) ` {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
        define dR where \<open>dR = (\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k}) ` {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
        have fin_d: \<open>finite d\<close> using division_of_finite[OF div] .
        have g_empty: \<open>g {} = 0\<close> using operative.empty[OF assms] .
        \<comment> \<open>Step 1: split axiom + triangle inequality\<close>
        have step1: \<open>(\<Sum>K\<in>d. norm (g K))
            \<le> (\<Sum>K\<in>d. norm (g (K \<inter> {x. x \<bullet> k \<le> c}))) + (\<Sum>K\<in>d. norm (g (K \<inter> {x. c \<le> x \<bullet> k})))\<close>
        proof -
          have \<open>(\<Sum>K\<in>d. norm (g K))
              \<le> (\<Sum>K\<in>d. norm (g (K \<inter> {x. x \<bullet> k \<le> c})) + norm (g (K \<inter> {x. c \<le> x \<bullet> k})))\<close>
          proof (rule sum_mono)
            fix K assume Kd: \<open>K \<in> d\<close>
            then obtain aK bK where K_eq: \<open>K = cbox aK bK\<close> using division_ofD(4)[OF div] by blast
            have \<open>g K = g (K \<inter> {x. x \<bullet> k \<le> c}) + g (K \<inter> {x. c \<le> x \<bullet> k})\<close>
              using local.split[OF \<open>k \<in> Basis\<close>, of aK bK c] K_eq by simp
            then show \<open>norm (g K) \<le> norm (g (K \<inter> {x. x \<bullet> k \<le> c})) + norm (g (K \<inter> {x. c \<le> x \<bullet> k}))\<close>
              by (metis norm_triangle_ineq)
          qed
          also have \<open>\<dots> = (\<Sum>K\<in>d. norm (g (K \<inter> {x. x \<bullet> k \<le> c}))) + (\<Sum>K\<in>d. norm (g (K \<inter> {x. c \<le> x \<bullet> k})))\<close>
            by (rule sum.distrib)
          finally show ?thesis .
        qed
        \<comment> \<open>Step 2: drop zero terms (where intersection is empty, g {} = 0)\<close>
        have step2L: \<open>(\<Sum>K\<in>d. norm (g (K \<inter> {x. x \<bullet> k \<le> c})))
            = (\<Sum>K\<in>{l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}. norm (g (K \<inter> {x. x \<bullet> k \<le> c})))\<close>
          by (rule sum.mono_neutral_right) (auto simp: fin_d g_empty)
        have step2R: \<open>(\<Sum>K\<in>d. norm (g (K \<inter> {x. c \<le> x \<bullet> k})))
            = (\<Sum>K\<in>{l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}. norm (g (K \<inter> {x. c \<le> x \<bullet> k})))\<close>
          by (rule sum.mono_neutral_right) (auto simp: fin_d g_empty)
        have collision_L: \<open>norm (g (K1 \<inter> {x. x \<bullet> k \<le> c})) = 0\<close>
          if K1d: \<open>K1 \<in> d\<close> and K2d: \<open>K2 \<in> d\<close> and neq: \<open>K1 \<noteq> K2\<close>
            and coll: \<open>K1 \<inter> {x. x \<bullet> k \<le> c} = K2 \<inter> {x. x \<bullet> k \<le> c}\<close>
          for K1 K2
        proof -
          obtain a1 b1 where K1_eq: \<open>K1 = cbox a1 b1\<close> using division_ofD(4)[OF div K1d] by blast
          have eq: \<open>K1 \<inter> {x. x \<bullet> k \<le> c} = cbox a1 (\<Sum>i\<in>Basis. (if i = k then min (b1 \<bullet> k) c else b1 \<bullet> i) *\<^sub>R i)\<close>
            using interval_split(1)[OF \<open>k \<in> Basis\<close>] K1_eq by simp
          have \<open>interior (K1 \<inter> {x. x \<bullet> k \<le> c}) \<subseteq> interior K1 \<inter> interior K2\<close>
            using coll by (metis inf.cobounded1 interior_mono le_inf_iff)
          also have \<open>\<dots> = {}\<close> using division_ofD(5)[OF div K1d K2d neq] .
          finally have \<open>box a1 (\<Sum>i\<in>Basis. (if i = k then min (b1 \<bullet> k) c else b1 \<bullet> i) *\<^sub>R i) = {}\<close>
            using eq interior_cbox by auto
          then show ?thesis using null eq by auto
        qed
        have collision_R: \<open>norm (g (K1 \<inter> {x. c \<le> x \<bullet> k})) = 0\<close>
          if K1d: \<open>K1 \<in> d\<close> and K2d: \<open>K2 \<in> d\<close> and neq: \<open>K1 \<noteq> K2\<close>
            and coll: \<open>K1 \<inter> {x. c \<le> x \<bullet> k} = K2 \<inter> {x. c \<le> x \<bullet> k}\<close>
          for K1 K2
        proof -
          obtain a1 b1 where K1_eq: \<open>K1 = cbox a1 b1\<close> using division_ofD(4)[OF div K1d] by blast
          have eq: \<open>K1 \<inter> {x. c \<le> x \<bullet> k} = cbox (\<Sum>i\<in>Basis. (if i = k then max (a1 \<bullet> k) c else a1 \<bullet> i) *\<^sub>R i) b1\<close>
            using interval_split(2)[OF \<open>k \<in> Basis\<close>] K1_eq by simp
          have \<open>interior (K1 \<inter> {x. c \<le> x \<bullet> k}) \<subseteq> interior K1 \<inter> interior K2\<close>
            using coll by (metis inf.cobounded1 interior_mono le_inf_iff)
          also have \<open>\<dots> = {}\<close> using division_ofD(5)[OF div K1d K2d neq] .
          finally have \<open>box (\<Sum>i\<in>Basis. (if i = k then max (a1 \<bullet> k) c else a1 \<bullet> i) *\<^sub>R i) b1 = {}\<close>
            using eq interior_cbox by auto
          then show ?thesis using null eq by auto
        qed
        have fin_filt: \<open>finite {l \<in> d. l \<inter> S \<noteq> {}}\<close> for S :: \<open>'a set\<close>
          using fin_d by auto
        have reindexL: \<open>(\<Sum>K\<in>dL. norm (g K))
            = (\<Sum>K\<in>{l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}. norm (g (K \<inter> {x. x \<bullet> k \<le> c})))\<close>
          unfolding dL_def
          using collision_L 
          by (subst sum.reindex_nontrivial[OF fin_filt]) (auto simp: o_def) 
        have reindexR: \<open>(\<Sum>K\<in>dR. norm (g K))
            = (\<Sum>K\<in>{l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}. norm (g (K \<inter> {x. c \<le> x \<bullet> k})))\<close>
          unfolding dR_def
          using collision_R
          by (subst sum.reindex_nontrivial[OF fin_filt]) (auto simp: o_def) 
        have step3L: \<open>(\<Sum>K\<in>{l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}. norm (g (K \<inter> {x. x \<bullet> k \<le> c})))
            = (\<Sum>K\<in>dL. norm (g K))\<close>
          using reindexL by simp
        have step3R: \<open>(\<Sum>K\<in>{l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}. norm (g (K \<inter> {x. c \<le> x \<bullet> k})))
            = (\<Sum>K\<in>dR. norm (g K))\<close>
          using reindexR by simp
        have split_ineq: \<open>(\<Sum>k\<in>d. norm (g k)) \<le> (\<Sum>k\<in>dL. norm (g k)) + (\<Sum>k\<in>dR. norm (g k))\<close>
          using step1 step2L step2R step3L step3R by linarith
        \<comment> \<open>Step 4: each half is < e/2\<close>
        have divL: \<open>dL division_of (t \<inter> {x. x \<bullet> k \<le> c})\<close>
          unfolding dL_def division_of_def
        proof (intro conjI ballI allI impI)
          show \<open>finite ((\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c}) ` {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}})\<close>
            using fin_d by auto
        next
          fix K assume \<open>K \<in> (\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c}) ` {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
          then obtain l where ld: \<open>l \<in> d\<close> and lne: \<open>l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}\<close> and Keq: \<open>K = l \<inter> {x. x \<bullet> k \<le> c}\<close>
            by auto
          obtain al bl where leq: \<open>l = cbox al bl\<close> using division_ofD(4)[OF div ld] by blast
          show \<open>K \<subseteq> t \<inter> {x. x \<bullet> k \<le> c}\<close> using Keq division_ofD(2)[OF div ld] by auto
          show \<open>K \<noteq> {}\<close> using Keq lne by auto
          show \<open>\<exists>a b. K = cbox a b\<close> using Keq leq interval_split(1)[OF \<open>k \<in> Basis\<close>] by blast
        next
          fix K1 K2
          assume K1m: \<open>K1 \<in> (\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c}) ` {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
            and K2m: \<open>K2 \<in> (\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c}) ` {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
            and neq: \<open>K1 \<noteq> K2\<close>
          obtain l1 where l1d: \<open>l1 \<in> d\<close> and K1eq: \<open>K1 = l1 \<inter> {x. x \<bullet> k \<le> c}\<close> using K1m by auto
          obtain l2 where l2d: \<open>l2 \<in> d\<close> and K2eq: \<open>K2 = l2 \<inter> {x. x \<bullet> k \<le> c}\<close> using K2m by auto
          have \<open>l1 \<noteq> l2\<close> using neq K1eq K2eq by auto
          then have \<open>interior l1 \<inter> interior l2 = {}\<close> using division_ofD(5)[OF div l1d l2d] by auto
          then show \<open>interior K1 \<inter> interior K2 = {}\<close>
            using K1eq K2eq by auto
        next
          show \<open>\<Union> ((\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c}) ` {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}) = t \<inter> {x. x \<bullet> k \<le> c}\<close>
            using division_ofD(6)[OF div] by auto
        qed
        have divR: \<open>dR division_of (t \<inter> {x. c \<le> x \<bullet> k})\<close>
          unfolding dR_def division_of_def
        proof (intro conjI ballI allI impI)
          show \<open>finite ((\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k}) ` {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}})\<close>
            using fin_d by auto
        next
          fix K assume \<open>K \<in> (\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k}) ` {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
          then obtain l where ld: \<open>l \<in> d\<close> and lne: \<open>l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}\<close> and Keq: \<open>K = l \<inter> {x. c \<le> x \<bullet> k}\<close>
            by auto
          obtain al bl where leq: \<open>l = cbox al bl\<close> using division_ofD(4)[OF div ld] by blast
          show \<open>K \<subseteq> t \<inter> {x. c \<le> x \<bullet> k}\<close> using Keq division_ofD(2)[OF div ld] by auto
          show \<open>K \<noteq> {}\<close> using Keq lne by auto
          show \<open>\<exists>a b. K = cbox a b\<close> using Keq leq interval_split(2)[OF \<open>k \<in> Basis\<close>] by blast
        next
          fix K1 K2
          assume K1m: \<open>K1 \<in> (\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k}) ` {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
            and K2m: \<open>K2 \<in> (\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k}) ` {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
            and neq: \<open>K1 \<noteq> K2\<close>
          obtain l1 where l1d: \<open>l1 \<in> d\<close> and K1eq: \<open>K1 = l1 \<inter> {x. c \<le> x \<bullet> k}\<close> using K1m by auto
          obtain l2 where l2d: \<open>l2 \<in> d\<close> and K2eq: \<open>K2 = l2 \<inter> {x. c \<le> x \<bullet> k}\<close> using K2m by auto
          have \<open>l1 \<noteq> l2\<close> using neq K1eq K2eq by auto
          then have \<open>interior l1 \<inter> interior l2 = {}\<close> using division_ofD(5)[OF div l1d l2d] by auto
          then show \<open>interior K1 \<inter> interior K2 = {}\<close>
            using K1eq K2eq by auto
        next
          show \<open>\<Union> ((\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k}) ` {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}) = t \<inter> {x. c \<le> x \<bullet> k}\<close>
            using division_ofD(6)[OF div] by auto
        qed
        have subL: \<open>t \<inter> {x. x \<bullet> k \<le> c} \<subseteq> cbox a b \<inter> {x. x \<bullet> k \<le> c}\<close> using sub by auto
        have subR: \<open>t \<inter> {x. c \<le> x \<bullet> k} \<subseteq> cbox a b \<inter> {x. c \<le> x \<bullet> k}\<close> using sub by auto
        have contentL: \<open>sum content dL < r1\<close>
        proof -
          have \<open>sum content dL
              \<le> sum (content \<circ> (\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c})) {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
            unfolding dL_def by (rule sum_image_le) (auto simp: fin_d content_pos_le)
          also have \<open>\<dots> \<le> sum content {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
          proof (rule sum_mono)
            fix l assume \<open>l \<in> {l \<in> d. l \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}}\<close>
            then have ld: \<open>l \<in> d\<close> by auto
            obtain al bl where leq: \<open>l = cbox al bl\<close> using division_ofD(4)[OF div ld] by blast
            have \<open>l \<inter> {x. x \<bullet> k \<le> c} = cbox al (\<Sum>i\<in>Basis. (if i = k then min (bl \<bullet> k) c else bl \<bullet> i) *\<^sub>R i)\<close>
              using interval_split(1)[OF \<open>k \<in> Basis\<close>] leq by simp
            moreover have \<open>cbox al (\<Sum>i\<in>Basis. (if i = k then min (bl \<bullet> k) c else bl \<bullet> i) *\<^sub>R i) \<subseteq> cbox al bl\<close>
              apply (rule subset_box_imp)
              apply (auto simp: inner_Basis if_distrib [of \<open>(*) _\<close>] cong: if_cong)
              done
            ultimately show \<open>(content \<circ> (\<lambda>l. l \<inter> {x. x \<bullet> k \<le> c})) l \<le> content l\<close>
              using content_subset leq by (simp add: o_def)
          qed
          also have \<open>\<dots> \<le> sum content d\<close>
            by (rule sum_mono2) (auto simp: fin_d content_pos_le)
          also have \<open>\<dots> < r1\<close> using content_bound by simp
          finally show ?thesis .
        qed
        have contentR: \<open>sum content dR < r2\<close>
        proof -
          have \<open>sum content dR
              \<le> sum (content \<circ> (\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k})) {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
            unfolding dR_def by (rule sum_image_le) (auto simp: fin_d content_pos_le)
          also have \<open>\<dots> \<le> sum content {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
          proof (rule sum_mono)
            fix l assume \<open>l \<in> {l \<in> d. l \<inter> {x. c \<le> x \<bullet> k} \<noteq> {}}\<close>
            then have ld: \<open>l \<in> d\<close> by auto
            obtain al bl where leq: \<open>l = cbox al bl\<close> using division_ofD(4)[OF div ld] by blast
            have \<open>l \<inter> {x. c \<le> x \<bullet> k} = cbox (\<Sum>i\<in>Basis. (if i = k then max (al \<bullet> k) c else al \<bullet> i) *\<^sub>R i) bl\<close>
              using interval_split(2)[OF \<open>k \<in> Basis\<close>] leq by simp
            moreover have \<open>cbox (\<Sum>i\<in>Basis. (if i = k then max (al \<bullet> k) c else al \<bullet> i) *\<^sub>R i) bl \<subseteq> cbox al bl\<close>
              apply (rule subset_box_imp)
              apply (auto simp: inner_Basis if_distrib [of \<open>(*) _\<close>] cong: if_cong)
              done
            ultimately show \<open>(content \<circ> (\<lambda>l. l \<inter> {x. c \<le> x \<bullet> k})) l \<le> content l\<close>
              using content_subset leq by (simp add: o_def)
          qed
          also have \<open>\<dots> \<le> sum content d\<close>
            by (rule sum_mono2) (auto simp: fin_d content_pos_le)
          also have \<open>\<dots> < r2\<close> using content_bound by simp
          finally show ?thesis .
        qed
        have halfL: \<open>(\<Sum>k\<in>dL. norm (g k)) < e / 2\<close> using L[OF divL subL contentL] .
        have halfR: \<open>(\<Sum>k\<in>dR. norm (g k)) < e / 2\<close> using R[OF divR subR contentR] .
        have halves: \<open>(\<Sum>k\<in>dL. norm (g k)) + (\<Sum>k\<in>dR. norm (g k)) < e\<close>
          using halfL halfR by linarith
        show \<open>(\<Sum>k\<in>d. norm (g k)) < e\<close>
          using split_ineq halves by linarith
      qed
    qed
  qed (use absolutely_setcontinuous_on_subset in fastforce)+
qed

lemma operative_absolutely_continuous_on:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  shows \<open>operative (\<and>) True (\<lambda>s. absolutely_continuous_on s f)\<close>
proof -
  define h where \<open>h \<equiv> \<lambda>S. if S = {} then 0 else f (Sup S) - f (Inf S)\<close>
  have op_h: \<open>operative (+) 0 h\<close> using operative_function_endpoint_diff[of f, folded h_def] .
  have op_ac_h: \<open>operative (\<and>) True (absolutely_setcontinuous_on h)\<close>
    using operative_absolutely_setcontinuous_on[OF op_h] .
  have h_eq: \<open>h k = f (Sup k) - f (Inf k)\<close> if \<open>k \<noteq> {}\<close> for k
    using that by (simp add: h_def)
  have sum_eq: \<open>(\<Sum>k\<in>d. norm (h k)) = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))\<close>
    if div: \<open>d division_of t\<close> for d t
    by (intro sum.cong refl arg_cong[where f=norm] h_eq) (use division_ofD(3)[OF div] in auto)
  have ac_eq: \<open>absolutely_setcontinuous_on h s = absolutely_setcontinuous_on (\<lambda>k. f (Sup k) - f (Inf k)) s\<close> for s
    unfolding absolutely_setcontinuous_on_def
    by (metis (lifting) local.sum_eq)
  show ?thesis
    using op_ac_h unfolding absolutely_continuous_on_def ac_eq .
qed

lemma absolutely_continuous_on_imp_has_bounded_variation_on:
  assumes \<open>absolutely_continuous_on s f\<close> \<open>bounded s\<close>
  shows \<open>has_bounded_variation_on f s\<close>
  using assms unfolding absolutely_continuous_on_def has_bounded_variation_on_def
proof -
  define h where \<open>h \<equiv> \<lambda>S. if S = {} then 0 else f (Sup S) - f (Inf S)\<close>
  assume ac: \<open>absolutely_setcontinuous_on (\<lambda>k. f (Sup k) - f (Inf k)) s\<close>
  assume \<open>bounded s\<close>
  have h_eq: \<open>h k = f (Sup k) - f (Inf k)\<close> if \<open>k \<in> d\<close> \<open>d division_of t\<close> for k d t
    using division_ofD(3)[OF that(2) that(1)] by (simp add: h_def)
  have sum_eq: \<open>(\<Sum>k\<in>d. norm (h k)) = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))\<close>
    if \<open>d division_of t\<close> for d t
    by (rule sum.cong) (auto simp: h_eq[OF _ that])
  have ac_h: \<open>absolutely_setcontinuous_on h s\<close>
    unfolding absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
    then obtain \<delta> where \<open>\<delta> > 0\<close> and \<delta>: \<open>\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
      (\<Sum>k\<in>d. content k) < \<delta> \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>\<close>
      using ac[unfolded absolutely_setcontinuous_on_def] by meson
    show \<open>\<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm (h k)) < \<epsilon>\<close>
      using \<open>\<delta> > 0\<close> \<delta> sum_eq by auto
  qed
  from absolutely_setcontinuous_on_imp_has_bounded_setvariation_on
    [OF operative_function_endpoint_diff[of f, folded h_def] this \<open>bounded s\<close>]
  show \<open>has_bounded_setvariation_on (\<lambda>k. f (Sup k) - f (Inf k)) s\<close>
    unfolding has_bounded_setvariation_on_def by (metis sum_eq)
qed

lemma Lipschitz_imp_absolutely_continuous:
  assumes "\<And>x y. x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> norm (f x - f y) \<le> B * \<bar>x - y\<bar>"
  shows "absolutely_continuous_on s f"
  unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
proof (intro allI impI)
  fix \<epsilon> :: real assume "\<epsilon> > 0"
  show "\<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>"
  proof (cases "B \<le> 0")
    case True
    show ?thesis
    proof (intro exI conjI allI impI)
      show "(1::real) > 0" by simp
    next
      fix d t assume H: "d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < 1"
      then have div: "d division_of t" and sub: "t \<subseteq> s" by auto
      have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>d. B * \<bar>Sup k - Inf k\<bar>)"
      proof (rule sum_mono)
        fix k assume kd: "k \<in> d"
        then obtain u v where uv: "k = cbox u v" using div division_ofD(4) by meson
        have kne: "k \<noteq> {}" using kd div division_ofD(3) by blast
        then have le: "u \<le> v" using uv by auto
        have "k \<subseteq> t" using div division_ofD(2) kd by blast
        then have "u \<in> s" "v \<in> s" using sub uv le by auto
        then have "norm (f v - f u) \<le> B * \<bar>v - u\<bar>" using assms by auto
        then show "norm (f (Sup k) - f (Inf k)) \<le> B * \<bar>Sup k - Inf k\<bar>"
          using uv le by simp
      qed
      also have "\<dots> \<le> (\<Sum>k\<in>d. 0)"
      proof (rule sum_mono)
        fix k assume kd: "k \<in> d"
        then obtain u v where uv: "k = cbox u v" using div division_ofD(4) by meson
        have kne: "k \<noteq> {}" using kd div division_ofD(3) by blast
        then have "u \<le> v" using uv by auto
        then have "\<bar>Sup k - Inf k\<bar> \<ge> 0" using uv by simp
        then show "B * \<bar>Sup k - Inf k\<bar> \<le> 0" using True
          by (simp add: mult_nonpos_nonneg)
      qed
      also have "\<dots> = 0" by simp
      finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>" using \<open>\<epsilon> > 0\<close> by linarith
    qed
  next
    case False
    then have Bpos: "B > 0" by linarith
    show ?thesis
    proof (intro exI conjI allI impI)
      show "\<epsilon> / B > 0" using \<open>\<epsilon> > 0\<close> Bpos by simp
    next
      fix d t assume H: "d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<epsilon> / B"
      then have div: "d division_of t" and sub: "t \<subseteq> s"
        and sm: "(\<Sum>k\<in>d. content k) < \<epsilon> / B" by auto
      have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>d. B * content k)"
      proof (rule sum_mono)
        fix k assume kd: "k \<in> d"
        then obtain u v where uv: "k = cbox u v" using div division_ofD(4) by meson
        have kne: "k \<noteq> {}" using kd div division_ofD(3) by blast
        then have le: "u \<le> v" using uv by auto
        have "k \<subseteq> t" using div division_ofD(2) kd by blast
        then have "u \<in> s" "v \<in> s" using sub uv le by auto
        then have "norm (f v - f u) \<le> B * \<bar>v - u\<bar>" using assms by auto
        also have "\<dots> = B * content k" using uv le by (simp add: content_real)
        finally show "norm (f (Sup k) - f (Inf k)) \<le> B * content k"
          using uv le by simp
      qed
      also have "\<dots> = B * (\<Sum>k\<in>d. content k)" by (simp add: sum_distrib_left)
      also have "\<dots> < B * (\<epsilon> / B)" using sm Bpos by (intro mult_strict_left_mono) auto
      also have "\<dots> = \<epsilon>" using Bpos by simp
      finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon>" .
    qed
  qed
qed

subsection \<open>Combining intervals\<close>

lemma absolutely_continuous_on_combine:
  assumes "absolutely_continuous_on {a..c} f"
    and "absolutely_continuous_on {c..b} f" and "a \<le> c" "c \<le> b"
  shows "absolutely_continuous_on {a..b} f"
proof -
  have split: \<open>absolutely_continuous_on {a..b} f =
    (absolutely_continuous_on ({a..b} \<inter> {x. x \<le> c}) f \<and>
     absolutely_continuous_on ({a..b} \<inter> {x. c \<le> x}) f)\<close>
    using operative.Basis_imp[OF operative_absolutely_continuous_on[of f],
      of 1 a b c] by (simp add: Basis_real_def inner_real_def)
  have \<open>{a..b} \<inter> {x::real. x \<le> c} = {a..c}\<close> using assms by auto
  moreover have \<open>{a..b} \<inter> {x::real. c \<le> x} = {c..b}\<close> using assms by auto
  ultimately show ?thesis using split assms by simp
qed

lemma absolutely_continuous_on_division:
  assumes "\<And>k. k \<in> d \<Longrightarrow> absolutely_continuous_on k f"
    "d division_of {a..b}"
  shows "absolutely_continuous_on {a..b} f"
proof -
  have \<open>comm_monoid_set.F (\<and>) True (\<lambda>s. absolutely_continuous_on s f) d
        = absolutely_continuous_on (cbox a b) f\<close>
    using operative.division[OF operative_absolutely_continuous_on assms(2)[unfolded cbox_interval[symmetric]]] .
  then have \<open>(finite d \<longrightarrow> (\<forall>k\<in>d. absolutely_continuous_on k f))
             = absolutely_continuous_on {a..b} f\<close>
    by (simp add: comm_monoid_set_F_and cbox_interval)
  moreover have \<open>finite d\<close> using division_ofD(1)[OF assms(2)] .
  ultimately show ?thesis using assms(1) by simp
qed

subsection \<open>Bilinear and product\<close>

lemma absolutely_continuous_on_bilinear:
  fixes h :: \<open>'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::euclidean_space\<close>
    and f :: \<open>real \<Rightarrow> 'a\<close> and g :: \<open>real \<Rightarrow> 'b\<close>
  assumes \<open>bilinear h\<close> 
    and f: \<open>absolutely_continuous_on s f\<close> 
    and g: \<open>absolutely_continuous_on s g\<close> 
    and s: \<open>is_interval s\<close> \<open>bounded s\<close>
  shows \<open>absolutely_continuous_on s (\<lambda>x. h (f x) (g x))\<close>
proof -
  have bv_f: \<open>has_bounded_variation_on f s\<close>
    using absolutely_continuous_on_imp_has_bounded_variation_on[OF f s(2)] .
  have bv_g: \<open>has_bounded_variation_on g s\<close>
    using absolutely_continuous_on_imp_has_bounded_variation_on[OF g s(2)] .
  have bd_f: \<open>bounded (f ` s)\<close>
    using has_bounded_variation_on_imp_bounded[OF bv_f s(1)] .
  have bd_g: \<open>bounded (g ` s)\<close>
    using has_bounded_variation_on_imp_bounded[OF bv_g s(1)] .
  obtain B1 where \<open>B1 > 0\<close> \<open>\<And>x. x \<in> s \<Longrightarrow> norm (f x) < B1\<close>
    using bd_f[unfolded bounded_pos_less] by (fastforce simp: image_iff)
  obtain B2 where \<open>B2 > 0\<close> \<open>\<And>x. x \<in> s \<Longrightarrow> norm (g x) < B2\<close>
    using bd_g[unfolded bounded_pos_less] by (fastforce simp: image_iff)
  obtain K where \<open>K > 0\<close> and K: \<open>\<And>x y. norm (h x y) \<le> K * norm x * norm y\<close>
    using bilinear_bounded_pos[OF assms(1)] by auto
  note bl = bilinear_ladd[OF assms(1)] bilinear_radd[OF assms(1)]
    bilinear_lsub[OF assms(1)] bilinear_rsub[OF assms(1)]
  have decomp: \<open>h (f (Sup k)) (g (Sup k)) - h (f (Inf k)) (g (Inf k)) =
    h (f (Sup k) - f (Inf k)) (g (Sup k)) + h (f (Inf k)) (g (Sup k) - g (Inf k))\<close> for k
    by (simp add: bl algebra_simps)
  show ?thesis
    unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
  proof (intro allI impI)
    fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
    have eB2K: \<open>\<epsilon> / 2 / B2 / K > 0\<close> using \<open>\<epsilon> > 0\<close> \<open>B2 > 0\<close> \<open>K > 0\<close> by simp
    have eB1K: \<open>\<epsilon> / 2 / B1 / K > 0\<close> using \<open>\<epsilon> > 0\<close> \<open>B1 > 0\<close> \<open>K > 0\<close> by simp
    obtain \<delta>1 where \<open>\<delta>1 > 0\<close> and \<delta>1: \<open>\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
      (\<Sum>k\<in>d. content k) < \<delta>1 \<Longrightarrow> (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / 2 / B2 / K\<close>
      using f unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
      using eB2K by (meson order.strict_trans2)
    obtain \<delta>2 where \<open>\<delta>2 > 0\<close> and \<delta>2: \<open>\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
      (\<Sum>k\<in>d. content k) < \<delta>2 \<Longrightarrow> (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) < \<epsilon> / 2 / B1 / K\<close>
      using g unfolding absolutely_continuous_on_def absolutely_setcontinuous_on_def
      using eB1K by (meson order.strict_trans2)
    show \<open>\<exists>\<delta>>0. \<forall>d t. d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < \<delta> \<longrightarrow>
      (\<Sum>k\<in>d. norm (h (f (Sup k)) (g (Sup k)) - h (f (Inf k)) (g (Inf k)))) < \<epsilon>\<close>
    proof (intro exI conjI allI impI)
      show \<open>min \<delta>1 \<delta>2 > 0\<close> using \<open>\<delta>1 > 0\<close> \<open>\<delta>2 > 0\<close> by simp
    next
      fix d t assume H: \<open>d division_of t \<and> t \<subseteq> s \<and> (\<Sum>k\<in>d. content k) < min \<delta>1 \<delta>2\<close>
      then have div: \<open>d division_of t\<close> and sub: \<open>t \<subseteq> s\<close>
        and meas: \<open>(\<Sum>k\<in>d. content k) < \<delta>1\<close> \<open>(\<Sum>k\<in>d. content k) < \<delta>2\<close> by auto
      have fin: \<open>finite d\<close> using division_of_finite[OF div] .
      have mem_s: \<open>Sup k \<in> s\<close> \<open>Inf k \<in> s\<close> if kd: \<open>k \<in> d\<close> for k
      proof -
        obtain u v where uv: \<open>k = cbox u v\<close>
          using division_ofD(4)[OF div kd] by blast
        have kne: \<open>k \<noteq> {}\<close> using division_ofD(3)[OF div kd] .
        then have le: \<open>u \<le> v\<close> using uv by (simp add: box_ne_empty)
        have ksub: \<open>k \<subseteq> s\<close> using division_ofD(2)[OF div kd] sub by auto
        have \<open>k = {u..v}\<close> using uv box_real by auto
        then show \<open>Sup k \<in> s\<close> \<open>Inf k \<in> s\<close>
          using le ksub by (auto simp: interval_bounds_real)
      qed
      \<comment> \<open>Main inequality chain\<close>
      have \<open>(\<Sum>k\<in>d. norm (h (f (Sup k)) (g (Sup k)) - h (f (Inf k)) (g (Inf k))))
        = (\<Sum>k\<in>d. norm (h (f (Sup k) - f (Inf k)) (g (Sup k)) +
                       h (f (Inf k)) (g (Sup k) - g (Inf k))))\<close>
        by (simp add: decomp)
      also have \<open>\<dots> \<le> (\<Sum>k\<in>d. norm (h (f (Sup k) - f (Inf k)) (g (Sup k))) +
                             norm (h (f (Inf k)) (g (Sup k) - g (Inf k))))\<close>
        by (intro sum_mono norm_triangle_ineq)
      also have \<open>\<dots> \<le> (\<Sum>k\<in>d. K * norm (f (Sup k) - f (Inf k)) * norm (g (Sup k)) +
                             K * norm (f (Inf k)) * norm (g (Sup k) - g (Inf k)))\<close>
        by (intro sum_mono add_mono K)
      also have \<open>\<dots> \<le> (\<Sum>k\<in>d. K * norm (f (Sup k) - f (Inf k)) * B2 +
                             K * B1 * norm (g (Sup k) - g (Inf k)))\<close>
      proof (intro sum_mono add_mono mult_left_mono mult_right_mono)
        fix k assume kd: \<open>k \<in> d\<close>
        show \<open>norm (g (Sup k)) \<le> B2\<close>
          using \<open>\<And>x. x \<in> s \<Longrightarrow> norm (g x) < B2\<close> mem_s(1)[OF kd] by (simp add: less_imp_le)
        show \<open>norm (f (Inf k)) \<le> B1\<close>
          using \<open>\<And>x. x \<in> s \<Longrightarrow> norm (f x) < B1\<close> mem_s(2)[OF kd] by (simp add: less_imp_le)
        show \<open>0 \<le> K * norm (f (Sup k) - f (Inf k))\<close>
          using \<open>K > 0\<close> by (simp add: mult_nonneg_nonneg)
        show \<open>0 \<le> norm (g (Sup k) - g (Inf k))\<close> by simp
        show \<open>0 \<le> K\<close> using \<open>K > 0\<close> by simp
      qed
      also have \<open>\<dots> = K * B2 * (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) +
                      K * B1 * (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))\<close>
        by (simp add: sum.distrib sum_distrib_left algebra_simps)
      also have \<open>\<dots> < \<epsilon> / 2 + \<epsilon> / 2\<close>
      proof -
        have KB2: \<open>K * B2 > 0\<close> using \<open>K > 0\<close> \<open>B2 > 0\<close> by simp
        have KB1: \<open>K * B1 > 0\<close> using \<open>K > 0\<close> \<open>B1 > 0\<close> by simp
        have f_bound: \<open>(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / 2 / B2 / K\<close>
          using \<delta>1[OF div sub meas(1)] .
        have g_bound: \<open>(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) < \<epsilon> / 2 / B1 / K\<close>
          using \<delta>2[OF div sub meas(2)] .
        have A: \<open>K * B2 * (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < \<epsilon> / 2\<close>
        proof -
          have \<open>K * B2 * (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) < K * B2 * (\<epsilon> / 2 / B2 / K)\<close>
            using mult_strict_left_mono[OF f_bound KB2] .
          also have \<open>\<dots> = \<epsilon> / 2\<close> using \<open>K > 0\<close> \<open>B2 > 0\<close> by (simp add: field_simps)
          finally show ?thesis .
        qed
        have B: \<open>K * B1 * (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) < \<epsilon> / 2\<close>
        proof -
          have \<open>K * B1 * (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) < K * B1 * (\<epsilon> / 2 / B1 / K)\<close>
            using mult_strict_left_mono[OF g_bound KB1] .
          also have \<open>\<dots> = \<epsilon> / 2\<close> using \<open>K > 0\<close> \<open>B1 > 0\<close> by (simp add: field_simps)
          finally show ?thesis .
        qed
        from A B show ?thesis by linarith
      qed
      also have \<open>\<dots> = \<epsilon>\<close> by simp
      finally show \<open>(\<Sum>k\<in>d. norm (h (f (Sup k)) (g (Sup k)) - h (f (Inf k)) (g (Inf k)))) < \<epsilon>\<close> .
    qed
  qed
qed

lemma absolutely_continuous_on_mul:
  fixes f :: \<open>real \<Rightarrow> real\<close> and g :: \<open>real \<Rightarrow> 'a::euclidean_space\<close>
  assumes \<open>absolutely_continuous_on s f\<close>
    \<open>absolutely_continuous_on s g\<close>
    \<open>is_interval s\<close> \<open>bounded s\<close>
  shows \<open>absolutely_continuous_on s (\<lambda>x. f x *\<^sub>R g x)\<close>
  using absolutely_continuous_on_bilinear
    [OF bilinear_conv_bounded_bilinear[THEN iffD2, OF bounded_bilinear_scaleR] assms] .

lemma absolutely_continuous_on_vsum:
  assumes \<open>finite k\<close>
    \<open>\<And>i. i \<in> k \<Longrightarrow> absolutely_continuous_on s (f i)\<close>
  shows \<open>absolutely_continuous_on s (\<lambda>x. \<Sum>i\<in>k. f i x)\<close>
  using assms
proof (induction k rule: finite_induct)
  case empty
  then show ?case by (simp add: absolutely_continuous_on_const)
next
  case (insert a F)
  then have \<open>absolutely_continuous_on s (f a)\<close>
    and \<open>absolutely_continuous_on s (\<lambda>x. \<Sum>i\<in>F. f i x)\<close> by auto
  then show ?case using insert.hyps
    by (simp add: absolutely_continuous_on_add)
qed

lemma absolutely_continuous_on_sing:
  \<open>absolutely_continuous_on {a} f\<close>
  using absolutely_continuous_on_null[of a a f] by (simp add: content_real_eq_0)


subsection \<open>Fundamental theorem of calculus\<close>

text \<open>
  Strong form of the fundamental theorem of calculus (Bartle's theorem).
  The derivative @{term f'} need only exist outside a negligible set @{term S},
  provided the \<open>Henstock–Sacks\<close> condition holds: for every @{term \<open>\<epsilon> > 0\<close>}
  there is a gauge witnessing that the oscillation of @{term f} over any
  fine tagged partial division with all tags in @{term S} is small.

  This is the Isabelle/HOL rendering of HOL Light's
  @{text FUNDAMENTAL_THEOREM_OF_CALCULUS_BARTLE}
  (Multivariate/integration.ml, line 22442).
\<close>

theorem fundamental_theorem_of_calculus_Bartle:
  fixes f :: \<open>real \<Rightarrow> 'a::euclidean_space\<close> and f' :: \<open>real \<Rightarrow> 'a\<close>
  assumes neg: \<open>negligible S\<close>
    and \<open>a \<le> b\<close>
    and deriv: \<open>\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})\<close>
    and HS: \<open>\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow>
                  \<exists>g. gauge g \<and>
                    (\<forall>p. p tagged_partial_division_of cbox a b \<and> g fine p \<and> fst ` p \<subseteq> S \<longrightarrow>
                      norm (\<Sum>(x,k)\<in>p. f (Sup k) - f (Inf k)) < \<epsilon>)\<close>
  shows \<open>(f' has_integral (f b - f a)) {a..b}\<close>
proof (cases \<open>a<b\<close>)
  case True
  define g where \<open>g \<equiv> (\<lambda>x. if x \<in> S then 0 else f' x)\<close>
  show ?thesis
  proof (rule has_integral_spike [OF neg])
   show "(g has_integral f b - f a) {a..b}"
      unfolding has_integral_real
    proof (intro strip)
      fix \<epsilon> :: real
      assume "0 < \<epsilon>"
      then obtain g1 where \<open>gauge g1\<close> 
           and g1: \<open>\<And>p. \<lbrakk>p tagged_partial_division_of cbox a b; g1 fine p; fst ` p \<subseteq> S\<rbrakk>
                   \<Longrightarrow> norm (\<Sum>(x,k)\<in>p. f (Sup k) - f (Inf k)) < \<epsilon>/2\<close>
        using HS[of \<open>\<epsilon>/2\<close>] by force

      have \<open>\<exists>d>0. (x \<in> {a..b} - S \<longrightarrow>
              (\<forall>y. \<bar>y - x\<bar> < d \<and> y \<in> {a..b} \<longrightarrow>
                norm (f y - f x - (y - x) *\<^sub>R g x) \<le> \<epsilon> / 2 / (b - a) * \<bar>y - x\<bar>))\<close> for x
      proof -
        show \<open>\<exists>d>0. x \<in> {a..b} - S \<longrightarrow>
                (\<forall>y. \<bar>y - x\<bar> < d \<and> y \<in> {a..b} \<longrightarrow>
                  norm (f y - f x - (y - x) *\<^sub>R g x) \<le> \<epsilon> / 2 / (b - a) * \<bar>y - x\<bar>)\<close>
        proof (cases \<open>x \<in> {a..b} - S\<close>)
          case False
          then show ?thesis
            by (intro exI[of _ 1]) auto
        next
          case True
          then have hvd: \<open>(f has_vector_derivative f' x) (at x within {a..b})\<close>
            using deriv by blast
          then have hd: \<open>(f has_derivative (\<lambda>h. h *\<^sub>R f' x)) (at x within {a..b})\<close>
            by (simp add: has_vector_derivative_def)
          have \<open>0 < \<epsilon> / 2 / (b - a)\<close>
            using \<open>0 < \<epsilon>\<close> \<open>a < b\<close> by simp
          with hd obtain d where \<open>d > 0\<close>
            and d: \<open>\<And>y. y \<in> {a..b} \<Longrightarrow> norm (y - x) < d \<Longrightarrow>
                       norm (f y - f x - (y - x) *\<^sub>R f' x) \<le> \<epsilon> / 2 / (b - a) * norm (y - x)\<close>
            unfolding has_derivative_within_alt by blast
          have gx: \<open>g x = f' x\<close>
            using True by (simp add: g_def)
          show ?thesis
          proof (intro exI conjI impI allI)
            show \<open>d > 0\<close> by fact
          next
            fix y
            assume \<open>x \<in> {a..b} - S\<close> \<open>\<bar>y - x\<bar> < d \<and> y \<in> {a..b}\<close>
            then show \<open>norm (f y - f x - (y - x) *\<^sub>R g x) \<le> \<epsilon> / 2 / (b - a) * \<bar>y - x\<bar>\<close>
              using d[of y] by (simp add: gx real_norm_def)
          qed
        qed
      qed
      then obtain d where dpos: \<open>\<And>x. d x >0\<close>
          and D: \<open>\<And>x. x \<in> {a..b} - S \<longrightarrow>
                      (\<forall>y. \<bar>y - x\<bar> < d x \<and> y \<in> {a..b} \<longrightarrow>
                      norm (f y - f x - (y - x) *\<^sub>R g x) \<le> \<epsilon> / 2 / (b - a) * \<bar>y - x\<bar>)\<close>
        by metis
      define \<gamma> where \<open>\<gamma> \<equiv> \<lambda>x. g1 x \<inter> ball x (d x)\<close>
      show "\<exists>\<gamma>. gauge \<gamma> \<and> (\<forall>\<D>. \<D> tagged_division_of {a..b} \<and> \<gamma> fine \<D> \<longrightarrow> norm ((\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R g x) - (f b - f a)) < \<epsilon>)"
      proof (intro exI conjI strip)
        show "gauge \<gamma>"
          by (simp add: \<gamma>_def \<open>gauge g1\<close> dpos gauge_Int gauge_ball_dependent)
      next
        fix \<D> :: "(real \<times> real set) set"
        assume "\<D> tagged_division_of {a..b} \<and> \<gamma> fine \<D>"
        then have *: \<open>(\<Sum>(x, K)\<in>\<D>. f (Sup K) - f (Inf K)) = f b - f a\<close>
          by (simp add: additive_tagged_division_1 assms)
        show "norm ((\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R g x) - (f b - f a)) < \<epsilon>"
        proof -
          have td: \<open>\<D> tagged_division_of {a..b}\<close> and fine: \<open>\<gamma> fine \<D>\<close>
            using \<open>\<D> tagged_division_of {a..b} \<and> \<gamma> fine \<D>\<close> by auto
          have tpd: \<open>\<D> tagged_partial_division_of cbox a b\<close>
            using td tagged_division_of_def by auto
          have g1_fine: \<open>g1 fine \<D>\<close>
            using fine unfolding \<gamma>_def by (auto simp: fine_Int)
          have ball_fine: \<open>(\<lambda>x. ball x (d x)) fine \<D>\<close>
            using fine unfolding \<gamma>_def by (auto simp: fine_Int)
          have \<D>_split: \<open>\<D> = {(x,k) \<in> \<D>. x \<in> S} \<union> {(x,k) \<in> \<D>. x \<notin> S}\<close>
            by auto
          define \<D>S where \<open>\<D>S \<equiv> {(x,k) \<in> \<D>. x \<in> S}\<close>
          define \<D>N where \<open>\<D>N \<equiv> {(x,k) \<in> \<D>. x \<notin> S}\<close>
          have sum_len: \<open>(\<Sum>(x, K)\<in>\<D>. Sup K - Inf K) = b - a\<close>
            using additive_tagged_division_1[OF \<open>a \<le> b\<close> td] .
          \<comment> \<open>S-component: < \<epsilon>/2\<close>
          have S_bound: \<open>norm (\<Sum>(x,k)\<in>\<D>S. f (Sup k) - f (Inf k)) < \<epsilon>/2\<close>
          proof (rule g1)
            show \<open>\<D>S tagged_partial_division_of cbox a b\<close>
              unfolding \<D>S_def using tpd tagged_partial_division_subset
              using \<D>_split by auto
            show \<open>g1 fine \<D>S\<close>
              using g1_fine fine_subset by (force simp: \<D>S_def fine_def)
            show \<open>fst ` \<D>S \<subseteq> S\<close>
              unfolding \<D>S_def by force
          qed
          \<comment> \<open>Non-S-component: \<le> \<epsilon>/2\<close>
          have N_bound: \<open>norm (\<Sum>(x,k)\<in>\<D>N. content k *\<^sub>R g x - (f (Sup k) - f (Inf k))) \<le> \<epsilon>/2\<close> (is "?L \<le> _")
          proof -
            \<comment> \<open>Fact 1: norm bound by per-element derivative bound\<close>
            have step1: \<open>?L \<le> (\<Sum>(x,k)\<in>\<D>N. \<epsilon> / 2 / (b - a) * (Sup k - Inf k))\<close>
            proof (rule sum_norm_le)
              fix xk assume xk_in: \<open>xk \<in> \<D>N\<close>
              obtain x k where xk: \<open>xk = (x, k)\<close> by (cases xk)
              with xk_in have mem: \<open>(x, k) \<in> \<D>\<close> \<open>x \<notin> S\<close>
                unfolding \<D>N_def by auto
              from td mem have xk_props: \<open>x \<in> k\<close> \<open>k \<subseteq> {a..b}\<close>
                by (auto dest: tagged_division_ofD)
              from td mem obtain c e where k_int: \<open>k = cbox c e\<close>
                using tagged_division_ofD(4) by blast
              with xk_props have ce: \<open>c \<le> e\<close> \<open>c \<le> x\<close> \<open>x \<le> e\<close>
                by auto
              have k_eq: \<open>k = {c..e}\<close> using k_int by auto
              have sup_k: \<open>Sup k = e\<close> and inf_k: \<open>Inf k = c\<close>
                using ce by (auto simp: k_eq)
              have cont: \<open>content k = Sup k - Inf k\<close>
                using ce content_real k_eq sup_k inf_k by auto
              have x_ab: \<open>x \<in> {a..b} - S\<close> using xk_props mem by auto
              \<comment> \<open>From ball-fineness: Sup k and Inf k are within d x of x\<close>
              have k_ball: \<open>k \<subseteq> ball x (d x)\<close>
                using ball_fine mem unfolding fine_def by auto
              have sup_in: \<open>Sup k \<in> k\<close> using ce by (auto simp: k_eq)
              have inf_in: \<open>Inf k \<in> k\<close> using ce by (auto simp: k_eq)
              have sup_ab: \<open>Sup k \<in> {a..b}\<close> using sup_in xk_props by auto
              have inf_ab: \<open>Inf k \<in> {a..b}\<close> using inf_in xk_props by auto
              have sup_near: \<open>\<bar>Sup k - x\<bar> < d x\<close>
                using k_ball sup_in by (auto simp: dist_real_def)
              have inf_near: \<open>\<bar>Inf k - x\<bar> < d x\<close>
                using k_ball inf_in by (auto simp: dist_real_def)
              \<comment> \<open>Apply derivative bound D at Sup k and Inf k\<close>
              have bnd_sup: \<open>norm (f (Sup k) - f x - (Sup k - x) *\<^sub>R g x)
                            \<le> \<epsilon> / 2 / (b - a) * \<bar>Sup k - x\<bar>\<close>
                using D x_ab sup_near sup_ab by auto
              have bnd_inf: \<open>norm (f (Inf k) - f x - (Inf k - x) *\<^sub>R g x)
                            \<le> \<epsilon> / 2 / (b - a) * \<bar>Inf k - x\<bar>\<close>
                using D x_ab inf_near inf_ab by auto
              \<comment> \<open>Algebraic decomposition\<close>
              have decomp: \<open>content k *\<^sub>R g x - (f (Sup k) - f (Inf k))
                          = (f (Inf k) - f x - (Inf k - x) *\<^sub>R g x)
                          - (f (Sup k) - f x - (Sup k - x) *\<^sub>R g x)\<close>
                by (simp add: cont sup_k inf_k algebra_simps)
              \<comment> \<open>Triangle inequality + derivative bounds\<close>
              have \<open>norm (content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))
                  \<le> norm (f (Inf k) - f x - (Inf k - x) *\<^sub>R g x)
                   + norm (f (Sup k) - f x - (Sup k - x) *\<^sub>R g x)\<close>
                unfolding decomp by (rule norm_triangle_ineq4)
              also have \<open>\<dots> \<le> \<epsilon> / 2 / (b - a) * \<bar>Inf k - x\<bar>
                           + \<epsilon> / 2 / (b - a) * \<bar>Sup k - x\<bar>\<close>
                using bnd_inf bnd_sup by linarith
              also have \<open>\<dots> = \<epsilon> / 2 / (b - a) * (Sup k - Inf k)\<close>
              proof -
                have abs1: \<open>\<bar>Inf k - x\<bar> = x - Inf k\<close> using ce sup_k inf_k by auto
                have abs2: \<open>\<bar>Sup k - x\<bar> = Sup k - x\<close> using ce sup_k inf_k by auto
                show ?thesis unfolding abs1 abs2
                  by (simp add: add_divide_distrib[symmetric] algebra_simps)
              qed
              finally show \<open>norm (case xk of (x,k) \<Rightarrow> content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))
                          \<le> (case xk of (x,k) \<Rightarrow> \<epsilon> / 2 / (b - a) * (Sup k - Inf k))\<close>
                by (simp add: xk)
            qed
            \<comment> \<open>Fact 2: subset monotonicity of nonneg sum\<close>
            have step2: \<open>(\<Sum>(x,k)\<in>\<D>N. \<epsilon> / 2 / (b - a) * (Sup k - Inf k))
                        \<le> (\<Sum>(x,k)\<in>\<D>.  \<epsilon> / 2 / (b - a) * (Sup k - Inf k))\<close>
            proof (rule sum_mono2)
              show \<open>finite \<D>\<close> using tagged_division_of_finite[OF td] .
              show \<open>\<D>N \<subseteq> \<D>\<close> unfolding \<D>N_def by auto
              fix xk assume \<open>xk \<in> \<D> - \<D>N\<close>
              then obtain x k where \<open>xk = (x,k)\<close> \<open>(x,k) \<in> \<D>\<close> by (cases xk) auto
              then obtain c e where \<open>k = cbox c e\<close> \<open>c \<le> e\<close>
                using tagged_division_ofD(4,2) td
                by (smt (verit) atLeastAtMost_iff box_real(2) subset_iff)
              then have \<open>Sup k \<ge> Inf k\<close> by simp
              then show \<open>0 \<le> (case xk of (x,k) \<Rightarrow> \<epsilon> / 2 / (b - a) * (Sup k - Inf k))\<close>
                using \<open>0 < \<epsilon>\<close> True \<open>xk = (x,k)\<close> by (auto intro!: mult_nonneg_nonneg)
            qed
            have sum_eq: \<open>(\<Sum>(x,k)\<in>\<D>. \<epsilon> / 2 / (b - a) * (Sup k - Inf k))
                        = \<epsilon> / 2 / (b - a) * (b - a)\<close>
            proof -
              have \<open>(\<Sum>(x,k)\<in>\<D>. \<epsilon> / 2 / (b - a) * (Sup k - Inf k))
                  = \<epsilon> / 2 / (b - a) * (\<Sum>(x,k)\<in>\<D>. Sup k - Inf k)\<close>
                by (auto simp: sum_distrib_left case_prod_unfold)
              also have \<open>\<dots> = \<epsilon> / 2 / (b - a) * (b - a)\<close>
                by (simp add: sum_len)
              finally show ?thesis .
            qed
            have \<open>?L \<le> \<epsilon> / 2 / (b - a) * (b - a)\<close>
              using step1 step2 sum_eq by linarith
            also have \<open>\<dots> = \<epsilon> / 2\<close>
              using True divide_eq_eq by fastforce
            finally show ?thesis .
          qed
          \<comment> \<open>Combine the two halves\<close>
          have fin\<D>: \<open>finite \<D>\<close> using tagged_division_of_finite[OF td] .
          have disj: \<open>\<D>S \<inter> \<D>N = {}\<close> unfolding \<D>S_def \<D>N_def by auto
          have union: \<open>\<D> = \<D>S \<union> \<D>N\<close> unfolding \<D>S_def \<D>N_def using \<D>_split by auto
          have fin_S: \<open>finite \<D>S\<close> and fin_N: \<open>finite \<D>N\<close>
            using fin\<D> union by (auto intro: finite_subset)
          \<comment> \<open>Rewrite goal using * and combine sums\<close>
          have \<open>norm ((\<Sum>(x,k)\<in>\<D>. content k *\<^sub>R g x) - (f b - f a))
              = norm (\<Sum>(x,k)\<in>\<D>. content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))\<close>
            by (smt (verit) "*" split_def sum.cong sum_subtractf)
          \<comment> \<open>Split into S and non-S parts\<close>
          also have \<open>\<dots> = norm ((\<Sum>(x,k)\<in>\<D>S. content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))
                            + (\<Sum>(x,k)\<in>\<D>N. content k *\<^sub>R g x - (f (Sup k) - f (Inf k))))\<close>
            by (simp add: sum.union_disjoint[OF fin_S fin_N disj, symmetric] union)
          \<comment> \<open>On \<D>S, g x = 0 so @{term\<open>content k *\<^sub>R g x = 0\<close>}\<close>
          also have \<open>(\<Sum>(x,k)\<in>\<D>S. content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))
                   = (\<Sum>(x,k)\<in>\<D>S. f (Inf k) - f (Sup k))\<close>
          proof (rule sum.cong[OF refl])
            fix xk assume \<open>xk \<in> \<D>S\<close>
            then obtain x k where \<open>xk = (x,k)\<close> \<open>x \<in> S\<close> unfolding \<D>S_def by auto
            then show \<open>(case xk of (x,k) \<Rightarrow> content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))
                     = (case xk of (x,k) \<Rightarrow> (f (Inf k) - f (Sup k)))\<close>
              by (simp add: g_def split: prod.splits)
          qed
          also have \<open>\<dots> = - (\<Sum>(x,k)\<in>\<D>S. f (Sup k) - f (Inf k))\<close>
            by (simp add: split_def sum_subtractf)
          also have \<open>norm (- (\<Sum>(x,k)\<in>\<D>S. f (Sup k) - f (Inf k))
                         + (\<Sum>(x,k)\<in>\<D>N. content k *\<^sub>R g x - (f (Sup k) - f (Inf k))))
                   \<le> norm (\<Sum>(x,k)\<in>\<D>S. f (Sup k) - f (Inf k))
                    + norm (\<Sum>(x,k)\<in>\<D>N. content k *\<^sub>R g x - (f (Sup k) - f (Inf k)))\<close>
            using norm_add_rule_thm norm_imp_pos_and_ge norm_minus_cancel by blast
          also have \<open>\<dots> < \<epsilon>/2 + \<epsilon>/2\<close>
            using S_bound N_bound by linarith
          also have \<open>\<dots> = \<epsilon>\<close> by simp
          finally show ?thesis .
        qed
      qed
    qed
  qed (auto simp: g_def)
next
  case False
  then show ?thesis
    using \<open>a \<le> b\<close> by force
qed

lemma negligible_content_gauge:
  fixes a b :: real
  assumes \<open>negligible S\<close> \<open>\<delta> > 0\<close>
  shows \<open>\<exists>g. gauge g \<and>
    (\<forall>p. p tagged_partial_division_of cbox a b \<and> g fine p \<and> fst ` p \<subseteq> S \<longrightarrow>
      (\<Sum>(x,k)\<in>p. content k) < \<delta>)\<close>
proof -
  have int: \<open>(indicat_real S has_integral 0) (cbox a b)\<close>
    using assms(1) negligible_def by blast
  then have intble: \<open>indicat_real S integrable_on cbox a b\<close>
    by (rule has_integral_integrable)
  obtain \<gamma> where \<open>gauge \<gamma>\<close> and \<gamma>:
    \<open>\<And>p. \<lbrakk>p tagged_partial_division_of cbox a b; \<gamma> fine p\<rbrakk>
     \<Longrightarrow> (\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R indicat_real S x - integral k (indicat_real S))) < \<delta>\<close>
    using Henstock_lemma[OF intble \<open>\<delta> > 0\<close>] by blast
  show ?thesis
  proof (intro exI conjI allI impI)
    show \<open>gauge \<gamma>\<close> by fact
    fix p assume asm: \<open>p tagged_partial_division_of cbox a b \<and> \<gamma> fine p \<and> fst ` p \<subseteq> S\<close>
    then have pd: \<open>p tagged_partial_division_of cbox a b\<close> and fine: \<open>\<gamma> fine p\<close> 
      and tags: \<open>fst ` p \<subseteq> S\<close> by auto
    have eq: \<open>content k *\<^sub>R indicat_real S x - integral k (indicat_real S) = content k\<close>
      if \<open>(x, k) \<in> p\<close> for x k
    proof -
      from that tags have \<open>x \<in> S\<close> by force
      then have \<open>indicat_real S x = 1\<close> by (simp add: indicator_def)
      moreover have \<open>integral k (indicat_real S) = 0\<close>
        by (metis assms(1) integral_unique negligible_def pd tagged_partial_division_ofD(4)
            that)
      ultimately show ?thesis by simp
    qed
    have \<open>(\<Sum>(x,k)\<in>p. content k) = (\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R indicat_real S x - integral k (indicat_real S)))\<close>
    proof (rule sum.cong)
      fix xk assume \<open>xk \<in> p\<close>
      then obtain x k where \<open>xk = (x, k)\<close> and \<open>(x, k) \<in> p\<close> by (cases xk) auto
      then show \<open>(case xk of (x, k) \<Rightarrow> content k) = (case xk of (x, k) \<Rightarrow> norm (content k *\<^sub>R indicat_real S x - integral k (indicat_real S)))\<close>
        using eq content_pos_le by (simp add: \<open>xk = (x, k)\<close>)
    qed auto
    also have \<open>\<dots> < \<delta>\<close>
      using \<gamma>[OF pd fine] .
    finally show \<open>(\<Sum>(x,k)\<in>p. content k) < \<delta>\<close> .
  qed
qed

lemma absolutely_continuous_on_imp_Henstock_Sacks:
  assumes \<open>negligible S\<close> \<open>absolutely_continuous_on {a..b} f\<close> \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>g. gauge g \<and>
    (\<forall>p. p tagged_partial_division_of cbox a b \<and> g fine p \<and> fst ` p \<subseteq> S \<longrightarrow>
      norm (\<Sum>(x,k)\<in>p. f (Sup k) - f (Inf k)) < \<epsilon>)\<close>
proof -
  define F where \<open>F \<equiv> \<lambda>k. f (Sup k) - f (Inf k)\<close>
  from assms(2) have ac: \<open>absolutely_setcontinuous_on F {a..b}\<close>
    unfolding absolutely_continuous_on_def F_def .
  then obtain \<delta> where \<open>\<delta> > 0\<close> and \<delta>:
    \<open>\<And>d t. \<lbrakk>d division_of t; t \<subseteq> {a..b}; sum content d < \<delta>\<rbrakk> \<Longrightarrow> (\<Sum>k\<in>d. norm (F k)) < \<epsilon>\<close>
    using assms(3) unfolding absolutely_setcontinuous_on_def by meson
  obtain g where \<open>gauge g\<close> and g:
    \<open>\<And>p. \<lbrakk>p tagged_partial_division_of cbox a b; g fine p; fst ` p \<subseteq> S\<rbrakk>
      \<Longrightarrow> (\<Sum>(x,k)\<in>p. content k) < \<delta>\<close>
    using negligible_content_gauge[OF assms(1) \<open>\<delta> > 0\<close>, of a b] by auto
  show ?thesis
  proof (intro exI conjI allI impI)
    show \<open>gauge g\<close> by fact
    fix p assume asm: \<open>p tagged_partial_division_of cbox a b \<and> g fine p \<and> fst ` p \<subseteq> S\<close>
    then have pd: \<open>p tagged_partial_division_of cbox a b\<close> and fine: \<open>g fine p\<close>
      and tags: \<open>fst ` p \<subseteq> S\<close> by auto
    have inj: \<open>inj_on snd p\<close>
    proof (rule inj_onI)
      fix xk1 xk2 assume \<open>xk1 \<in> p\<close> \<open>xk2 \<in> p\<close> \<open>snd xk1 = snd xk2\<close>
      then obtain x1 K1 x2 K2 where eq: \<open>xk1 = (x1, K1)\<close> \<open>xk2 = (x2, K2)\<close> \<open>K1 = K2\<close>
        by (cases xk1; cases xk2) auto
      show \<open>xk1 = xk2\<close>
      proof (rule ccontr)
        assume \<open>xk1 \<noteq> xk2\<close>
        with eq \<open>xk1 \<in> p\<close> \<open>xk2 \<in> p\<close> pd
        have \<open>interior K1 \<inter> interior K2 = {}\<close>
          using tagged_partial_division_ofD(5) by blast
        with eq have \<open>interior K1 = {}\<close> by auto
        moreover from \<open>xk1 \<in> p\<close> pd eq obtain c d where \<open>K1 = cbox c d\<close>
          using tagged_partial_division_ofD(4) by blast
        ultimately have \<open>box c d = {}\<close> using interior_cbox by metis
        moreover from \<open>xk1 \<in> p\<close> pd eq have \<open>x1 \<in> K1\<close> using tagged_partial_division_ofD(2) by blast
        moreover from \<open>xk2 \<in> p\<close> pd eq have \<open>x2 \<in> K1\<close> using tagged_partial_division_ofD(2) by blast
        ultimately have \<open>x1 = x2\<close> using \<open>K1 = cbox c d\<close> by (simp add: mem_box)
        with eq show False using \<open>xk1 \<noteq> xk2\<close> by auto
      qed
    qed
    have div: \<open>snd ` p division_of \<Union>(snd ` p)\<close>
      using partial_division_of_tagged_division[OF pd] .
    have sub: \<open>\<Union>(snd ` p) \<subseteq> {a..b}\<close>
    proof
      fix x assume \<open>x \<in> \<Union>(snd ` p)\<close>
      then obtain K where \<open>K \<in> snd ` p\<close> \<open>x \<in> K\<close> by auto
      then obtain xk where \<open>xk \<in> p\<close> \<open>snd xk = K\<close> by auto
      then obtain t where \<open>(t, K) \<in> p\<close> by (cases xk) auto
      then have \<open>K \<subseteq> cbox a b\<close> using tagged_partial_division_ofD(3)[OF pd] by blast
      with \<open>x \<in> K\<close> show \<open>x \<in> {a..b}\<close> by auto
    qed
    have content_bound: \<open>sum content (snd ` p) < \<delta>\<close>
    proof -
      have \<open>sum content (snd ` p) = (\<Sum>(x,k)\<in>p. content k)\<close>
        using sum.reindex[OF inj, of content] by (simp add: o_def case_prod_unfold)
      also have \<open>\<dots> < \<delta>\<close> using g[OF pd fine tags] .
      finally show ?thesis .
    qed
    have \<open>(\<Sum>k\<in>snd ` p. norm (F k)) < \<epsilon>\<close>
      using \<delta>[OF div sub content_bound] .
    then have \<open>(\<Sum>(x,k)\<in>p. norm (F k)) < \<epsilon>\<close>
      using sum.reindex[OF inj, of \<open>\<lambda>k. norm (F k)\<close>] by (simp add: o_def case_prod_unfold)
    moreover have \<open>norm (\<Sum>(x,k)\<in>p. F k) \<le> (\<Sum>(x,k)\<in>p. norm (F k))\<close>
    proof -
      have \<open>norm (sum (\<lambda>xk. F (snd xk)) p) \<le> (\<Sum>xk\<in>p. norm (F (snd xk)))\<close>
        by (rule norm_sum)
      then show ?thesis
        by (simp add: case_prod_unfold)
    qed
    ultimately show \<open>norm (\<Sum>(x,k)\<in>p. f (Sup k) - f (Inf k)) < \<epsilon>\<close>
      unfolding F_def by linarith
  qed
qed

theorem fundamental_theorem_of_calculus_absolutely_continuous:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "negligible S" "a \<le> b"
    "absolutely_continuous_on {a..b} f"
    "\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})"
  shows "(f' has_integral (f b - f a)) {a..b}"
proof (rule fundamental_theorem_of_calculus_Bartle)
  show \<open>negligible S\<close> \<open>a \<le> b\<close> by fact+
  show \<open>\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})\<close>
    using assms(4) .
  fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>
  \<comment> \<open>Need: absolutely_continuous_on \<Longrightarrow> Henstock–Sacks condition\<close>
  show \<open>\<exists>g. gauge g \<and>
        (\<forall>p. p tagged_partial_division_of cbox a b \<and> g fine p \<and> fst ` p \<subseteq> S \<longrightarrow>
          norm (\<Sum>(x,k)\<in>p. f (Sup k) - f (Inf k)) < \<epsilon>)\<close>
    using \<open>0 < \<epsilon>\<close> absolutely_continuous_on_imp_Henstock_Sacks assms(1,3) by fastforce
qed

subsection \<open>Closure and interior\<close>

lemma absolutely_continuous_on_closure:
  assumes "absolutely_continuous_on (interior s) f"
    "continuous_on (closure s) f" "is_interval s"
  shows "absolutely_continuous_on s f"
  sorry

end
