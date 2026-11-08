theory Quantitative_Finish
  imports Complex_Main
begin

text \<open>Green, Section 6 ("Completion of the proof"), after equation
  (6.1): the sum over the second row index is bounded below by
  \<open>S * k - k\<^sup>2\<close>.\<close>

lemma green_min_sum_reversed:
  fixes S k :: nat
  shows "(\<Sum>s<S. min k (S - 1 - s)) = (\<Sum>s<S. min k s)"
proof -
  have eq: "(\<Sum>s<S. min k s) = (\<Sum>s<S. min k (S - Suc s))"
    using sum.atLeastLessThan_rev[of "\<lambda>s. min k s" 0 S]
    by (simp add: atLeast0LessThan)
  have "(\<Sum>s<S. min k (S - 1 - s)) =
      (\<Sum>s<S. min k (S - Suc s))" by simp
  also have "... = (\<Sum>s<S. min k s)" by (rule eq[symmetric])
  finally show ?thesis .
qed

lemma green_min_sum_add_bound:
  fixes S k :: nat
  shows "S * k \<le> k * k + (\<Sum>s<S. min k s)"
proof (induction S)
  case 0
  then show ?case by simp
next
  case (Suc S)
  show ?case
  proof (cases "k \<le> S")
    case True
    with Suc.IH show ?thesis
      by (simp add: sum.lessThan_Suc; linarith)
  next
    case False
    then have "Suc S \<le> k" by simp
    then have "Suc S * k \<le> k * k" by (rule mult_right_mono) simp
    then show ?thesis by simp
  qed
qed

lemma green_min_sum_lower:
  fixes S k :: nat
  shows "S * k - k * k \<le> (\<Sum>s<S. min k (S - 1 - s))"
proof -
  have "S * k \<le> k * k + (\<Sum>s<S. min k (S - 1 - s))"
    using green_min_sum_add_bound[of S k] green_min_sum_reversed[where S=S and k=k]
    by arith
  then show ?thesis by arith
qed



lemma green_double_min_sum_bound:
  fixes R S p :: nat
  shows "S * (\<Sum>r<R. r div p) \<le>
    (\<Sum>r<R. (r div p) * (r div p)) +
    (\<Sum>r<R. \<Sum>s<S. min (r div p) (S - 1 - s))"
proof -
  have point: "S * (r div p) \<le> (r div p) * (r div p) +
      (\<Sum>s<S. min (r div p) (S - 1 - s))" for r
    using green_min_sum_add_bound[of S "r div p"]
      green_min_sum_reversed[where S=S and k="r div p"]
    by arith
  have "(\<Sum>r<R. S * (r div p)) \<le>
      (\<Sum>r<R. (r div p) * (r div p) +
        (\<Sum>s<S. min (r div p) (S - 1 - s)))"
    by (rule sum_mono) (rule point)
  then show ?thesis by (simp add: sum.distrib sum_distrib_left)
qed

lemma green_floor_point_lower:
  fixes r p :: nat
  assumes p: "0 < p"
  shows "real r / real p \<le> real (r div p) + 1"
proof -
  have eq: "real r / real p = real (r div p) + real (r mod p) / real p"
    by (rule of_nat_of_nat_div_aux)
  have "real (r mod p) \<le> real p" using p by simp
  then have "real (r mod p) / real p \<le> 1"
    using p by (simp add: divide_le_eq)
  with eq show ?thesis by linarith
qed

lemma green_floor_sum_lower:
  fixes R p :: nat
  assumes p: "0 < p"
  shows "(\<Sum>r<R. real r / real p) \<le>
    (\<Sum>r<R. real (r div p)) + real R"
proof -
  have "(\<Sum>r<R. real r / real p) \<le>
      (\<Sum>r<R. real (r div p) + 1)"
    by (rule sum_mono) (use green_floor_point_lower[OF p] in simp)
  also have "... = (\<Sum>r<R. real (r div p)) + real R"
    by (simp add: sum.distrib)
  finally show ?thesis .
qed


lemma green_floor_square_sum_bound:
  fixes R p :: nat
  assumes p: "0 < p"
  shows "(\<Sum>r<R. (real (r div p))^2) \<le>
    real R * (real R / real p)^2"
proof -
  have point: "(real (r div p))^2 \<le> (real R / real p)^2"
    if r: "r < R" for r
  proof -
    have "real (r div p) \<le> real r / real p"
      by (rule of_nat_div_le_of_nat)
    also have "... \<le> real R / real p"
      using p r by (intro divide_right_mono) auto
    finally show ?thesis by (intro power_mono) simp_all
  qed
  have "(\<Sum>r<R. (real (r div p))^2) \<le>
      (\<Sum>r<R. (real R / real p)^2)"
    by (rule sum_mono) (use point in simp)
  then show ?thesis by simp
qed

lemma green_index_sum:
  fixes R :: nat
  shows "2 * (\<Sum>r<R. real r) + real R = (real R)^2"
proof (induction R)
  case 0
  then show ?case by simp
next
  case (Suc R)
  have "2 * (\<Sum>r<Suc R. real r) + real (Suc R) =
      (2 * (\<Sum>r<R. real r) + real R) + 2 * real R + 1"
    by (simp add: sum.lessThan_Suc algebra_simps)
  also have "... = (real R)^2 + 2 * real R + 1"
    using Suc.IH by simp
  also have "... = (real (Suc R))^2" by (simp add: power2_eq_square algebra_simps)
  finally show ?case .
qed

lemma green_floor_sum_quadratic:
  fixes R p :: nat
  assumes p: "0 < p"
  shows "((real R)^2 - real R) / (2 * real p) \<le>
    (\<Sum>r<R. real (r div p)) + real R"
proof -
  have idx2: "2 * (\<Sum>r<R. real r) = (real R)^2 - real R"
    using green_index_sum[of R] by linarith
  have idx: "(\<Sum>r<R. real r) = ((real R)^2 - real R) / 2"
  proof -
    have "(\<Sum>r<R. real r) = (2 * (\<Sum>r<R. real r)) / 2" by simp
    also have "... = ((real R)^2 - real R) / 2" by (simp only: idx2)
    finally show ?thesis .
  qed
  have eq: "(\<Sum>r<R. real r / real p) =
      ((real R)^2 - real R) / (2 * real p)"
  proof -
    have "(\<Sum>r<R. real r / real p) =
        (\<Sum>r<R. real r) / real p"
      by (rule sum_divide_distrib[symmetric])
    also have "... = ((real R)^2 - real R) / (2 * real p)"
      by (simp add: idx)
    finally show ?thesis .
  qed
  show ?thesis using green_floor_sum_lower[OF p, of R] by (simp add: eq)
qed


lemma green_double_min_sum_real_bound:
  fixes R S p :: nat
  assumes p: "0 < p"
  shows "real S * (((real R)^2 - real R) / (2 * real p) - real R) \<le>
    (\<Sum>r<R. \<Sum>s<S. real (min (r div p) (S - 1 - s))) +
    real R * (real R / real p)^2"
proof -
  let ?Q = "((real R)^2 - real R) / (2 * real p)"
  let ?F = "(\<Sum>r<R. real (r div p))"
  let ?M = "(\<Sum>r<R. \<Sum>s<S. real (min (r div p) (S - 1 - s)))"
  let ?E = "(\<Sum>r<R. (real (r div p))^2)"
  have cast: "(real (S * (\<Sum>r<R. r div p)) :: real) \<le>
      real ((\<Sum>r<R. (r div p) * (r div p)) +
        (\<Sum>r<R. \<Sum>s<S. min (r div p) (S - 1 - s)))"
    by (rule of_nat_mono[OF green_double_min_sum_bound[where R=R and S=S and p=p]])
  have base: "real S * ?F \<le> ?E + ?M"
    using cast by (simp add: power2_eq_square)
  have floor: "?Q \<le> ?F + real R"
    by (rule green_floor_sum_quadratic[OF p])
  have scale: "real S * (?Q - real R) \<le> real S * ?F"
  proof (rule mult_left_mono)
    show "?Q - real R \<le> ?F" using floor by linarith
    show "0 \<le> real S" by simp
  qed
  have err: "?E \<le> real R * (real R / real p)^2"
    by (rule green_floor_square_sum_bound[OF p])
  show ?thesis using scale base err by linarith
qed


text \<open>In Green's application, the weight below is \<open>log p\<close> and
  the finite set consists of the inert primes up to \<open>X\<close>.\<close>

definition green_min_mass :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "green_min_mass R S p =
    (\<Sum>r<R. \<Sum>s<S. real (min (r div p) (S - 1 - s)))"


definition green_floor_main_term :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "green_floor_main_term R p =
    ((real R)^2 - real R) / (2 * real p) - real R"

definition green_floor_error :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "green_floor_error R p = real R * (real R / real p)^2"

lemma green_weighted_min_mass_bound:
  fixes P :: "nat set" and w :: "nat \<Rightarrow> real"
  assumes finite: "finite P"
    and positive: "\<And>p. p \<in> P \<Longrightarrow> 0 < p"
    and weight: "\<And>p. p \<in> P \<Longrightarrow> 0 \<le> w p"
    and valuation: "(\<Sum>p\<in>P. 2 * w p * green_min_mass R S p) \<le> H"
  shows "(\<Sum>p\<in>P. 2 * w p * real S *
      green_floor_main_term R p) \<le>
    H + (\<Sum>p\<in>P. 2 * w p * green_floor_error R p)"
proof -
  have point: "2 * w p * real S *
        green_floor_main_term R p \<le>
      2 * w p * green_min_mass R S p +
        2 * w p * green_floor_error R p"
    if pP: "p \<in> P" for p
  proof -
    have b: "real S *
        green_floor_main_term R p \<le>
      green_min_mass R S p + green_floor_error R p"
      using green_double_min_sum_real_bound[OF positive[OF pP], where R=R and S=S]
      by (simp add: green_min_mass_def green_floor_main_term_def green_floor_error_def)
    have "(2 * w p) * (real S *
        green_floor_main_term R p) \<le>
      (2 * w p) * (green_min_mass R S p + green_floor_error R p)"
      by (rule mult_left_mono[OF b]) (use weight[OF pP] in simp)
    then show ?thesis by (simp add: algebra_simps)
  qed
  have "(\<Sum>p\<in>P. 2 * w p * real S *
      green_floor_main_term R p) \<le>
    (\<Sum>p\<in>P. 2 * w p * green_min_mass R S p +
      2 * w p * green_floor_error R p)"
    by (rule sum_mono) (use point in auto)
  also have "... = (\<Sum>p\<in>P. 2 * w p * green_min_mass R S p) +
      (\<Sum>p\<in>P. 2 * w p * green_floor_error R p)"
    by (rule sum.distrib)
  also have "... \<le> H + (\<Sum>p\<in>P. 2 * w p * green_floor_error R p)"
    using valuation by simp
  finally show ?thesis .
qed

end
