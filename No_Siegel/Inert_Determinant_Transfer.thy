theory Inert_Determinant_Transfer
  imports Inert_Transform_Order Gram_Transformation
begin

lemma green_quad_coeff_int_linear:
  assumes irrational: "cpx_sqrt d \<notin> Rats"
  shows "green_quad_coeff d
      (\<Sum>i\<in>I. of_int (c i) * green_quad_embed d (f i)) =
    ((\<Sum>i\<in>I. c i * fst (f i)),
     (\<Sum>i\<in>I. c i * snd (f i)))"
proof -
  have embed:
    "(\<Sum>i\<in>I. of_int (c i) * green_quad_embed d (f i)) =
      green_quad_embed d
        ((\<Sum>i\<in>I. c i * fst (f i)),
         (\<Sum>i\<in>I. c i * snd (f i)))"
    by (simp add: green_quad_embed_def sum.distrib sum_distrib_left
      algebra_simps)
  show ?thesis
    by (simp add: embed green_quad_coeff_embed[OF irrational])
qed

lemma (in green_quadratic_character) green_transformed_row_coeff_binomial:
  assumes ppos: "0 < p"
    and grid: "P \<in> diagonal_grid (cpx_sqrt d) (natural_grid N)"
    and h: "h = green_inert_h p S (r,s)"
  shows "green_transformed_row_coeff d p S (r,s) (P,j) =
    ((\<Sum>i\<le>h. ((-1::int)^i * int (h choose i)) *
       fst (green_row_gram_coeff d (r-p*i,s+i) (P,j))),
     (\<Sum>i\<le>h. ((-1::int)^i * int (h choose i)) *
       snd (green_row_gram_coeff d (r-p*i,s+i) (P,j))))"
proof -
  have ph: "p*h \<le> r"
  proof -
    have "h \<le> r div p" using h by (simp add: green_inert_h_def)
    then have "p*h \<le> p*(r div p)" by (intro mult_left_mono; simp)
    also have "... \<le> r"
      using div_mult_mod_eq[of r p] by (simp add: mult.commute)
    finally show ?thesis .
  qed
  have row: "green_quad_embed d
       (green_row_gram_coeff d (r-p*i,s+i) (P,j)) =
       green_row_value (r-p*i,s+i) j P" for i
    by (simp add: green_row_gram_coeff_def
      green_quad_embed_coeff[OF green_lattice_grid_row_quadratic_integer[OF grid]])
  have val: "poly ((pderiv ^^ j)
      (green_transformed_row_poly p h r s (snd P))) (fst P) =
    (\<Sum>i\<le>h. of_int ((-1::int)^i * int (h choose i)) *
      green_quad_embed d (green_row_gram_coeff d (r-p*i,s+i) (P,j)))"
  proof -
    have expand: "poly ((pderiv ^^ j)
        (green_transformed_row_poly p h r s (snd P))) (fst P) =
      (\<Sum>i\<le>h. ((-1)^i * of_nat (h choose i)) *
        green_row_value (r-p*i,s+i) j P)"
      by (rule green_transformed_row_value_expand[OF ph])
    show ?thesis using expand by (simp add: row)
  qed
  have coeff: "green_quad_coeff d
      (\<Sum>i\<le>h. of_int ((-1::int)^i * int (h choose i)) *
        green_quad_embed d (green_row_gram_coeff d (r-p*i,s+i) (P,j))) =
    ((\<Sum>i\<le>h. ((-1::int)^i * int (h choose i)) *
        fst (green_row_gram_coeff d (r-p*i,s+i) (P,j))),
     (\<Sum>i\<le>h. ((-1::int)^i * int (h choose i)) *
        snd (green_row_gram_coeff d (r-p*i,s+i) (P,j))))"
    by (rule green_quad_coeff_int_linear[OF lattice_slope_irrational])
  show ?thesis
    using val coeff h by (simp add: green_transformed_row_coeff_def)
qed

lemma green_inert_row_shift_nth:
  assumes p: "0 < p" and a: "a < R*S"
    and k: "k = green_row_order R S ! a"
    and h: "h = green_inert_h p S k"
    and i: "i \<le> h"
  shows "green_row_order R S !
      ((fst k-p*i)*S+(snd k+i)) = (fst k-p*i,snd k+i)"
proof (cases "i=0")
  case True
  have ae: "a = fst k*S+snd k"
    unfolding k by (rule green_row_order_nth_index_eq[OF a])
  show ?thesis using k ae True by simp
next
  case False
  have r: "fst k < R" and s: "snd k < S"
    unfolding k by (rule green_row_order_nth_bounds[OF a])+
  have ae: "a = fst k*S+snd k"
    unfolding k by (rule green_row_order_nth_index_eq[OF a])
  have ipos: "0 < i" using False by simp
  have ih: "i \<le> green_inert_h p S (fst k,snd k)"
    using i h by simp
  show ?thesis
    by (rule green_inert_lower_row_index(2)[OF p r s ipos ih refl ae])
qed

lemma (in green_quadratic_character) green_transformed_coeff_matrix_row:
  assumes p: "0 < p"
    and grid: "P \<in> diagonal_grid (cpx_sqrt d) (natural_grid N)"
    and a: "a < R*S"
  shows "green_transformed_row_coeff d p S
      (green_row_order R S ! a) (P,j) =
    ((\<Sum>b<R*S. green_row_transform_matrix p R S $$ (a,b) *
        fst (green_row_gram_coeff d (green_row_order R S ! b) (P,j))),
     (\<Sum>b<R*S. green_row_transform_matrix p R S $$ (a,b) *
        snd (green_row_gram_coeff d (green_row_order R S ! b) (P,j))))"
proof -
  let ?k = "green_row_order R S ! a"
  let ?h = "green_inert_h p S ?k"
  let ?U = "green_row_transform_matrix p R S"
  let ?b = "\<lambda>i. (fst ?k-p*i)*S+(snd ?k+i)"
  let ?c = "\<lambda>i. (-1::int)^i * int (?h choose i)"
  have index: "green_row_order R S ! ?b i =
      (fst ?k-p*i,snd ?k+i)" if "i \<le> ?h" for i
    by (rule green_inert_row_shift_nth[OF p a refl refl that])
  have linear: "(\<Sum>b<R*S. ?U $$ (a,b) *
      q (green_row_gram_coeff d (green_row_order R S ! b) (P,j))) =
    (\<Sum>i\<le>?h. ?c i *
      q (green_row_gram_coeff d (fst ?k-p*i,snd ?k+i) (P,j)))"
    for q :: "int \<times> int \<Rightarrow> int"
  proof -
    have action: "(\<Sum>b<R*S. ?U $$ (a,b) *
        q (green_row_gram_coeff d (green_row_order R S ! b) (P,j))) =
      (\<Sum>i\<le>?h. ?c i *
        q (green_row_gram_coeff d (green_row_order R S ! ?b i) (P,j)))"
      by (rule green_row_transform_matrix_action_binomial[OF p a refl refl])
    show ?thesis
      unfolding action
      by (intro sum.cong; simp add: index)
  qed
  have bin:
    "green_transformed_row_coeff d p S ?k (P,j) =
      ((\<Sum>i\<le>?h. ?c i *
         fst (green_row_gram_coeff d
           (fst ?k-p*i,snd ?k+i) (P,j))),
       (\<Sum>i\<le>?h. ?c i *
         snd (green_row_gram_coeff d
           (fst ?k-p*i,snd ?k+i) (P,j))))"
  proof -
    have eq: "green_transformed_row_coeff d p S
        (fst ?k,snd ?k) (P,j) =
      ((\<Sum>i\<le>?h. ?c i *
         fst (green_row_gram_coeff d
           (fst ?k-p*i,snd ?k+i) (P,j))),
       (\<Sum>i\<le>?h. ?c i *
         snd (green_row_gram_coeff d
           (fst ?k-p*i,snd ?k+i) (P,j))))"
      by (rule green_transformed_row_coeff_binomial[OF p grid]) simp
    show ?thesis using eq by simp
  qed
  show ?thesis using bin linear[of fst] linear[of snd] by simp
qed

lemma (in green_quadratic_character) green_inert_gram_determinant_eq:
  assumes p: "0 < p"
    and P: "P \<subseteq> diagonal_grid (cpx_sqrt d) (natural_grid N)"
  shows "green_gram_determinant d (P \<times> {..<J})
      (green_transformed_row_coeff d p S) (green_row_order R S) =
    green_row_gram_determinant d P J R S"
proof -
  let ?n = "R*S"
  let ?I = "P \<times> {..<J}"
  let ?ks = "green_row_order R S"
  let ?U = "green_row_transform_matrix p R S"
  let ?f = "\<lambda>a t. green_row_gram_coeff d (?ks ! a) t"
  let ?f' = "\<lambda>a t. green_transformed_row_coeff d p S (?ks ! a) t"
  have U: "?U \<in> carrier_mat ?n ?n"
    by (rule green_row_transform_matrix_carrier)
  have det: "det ?U = 1" by (rule green_row_transform_matrix_det[OF p])
  have linear: "fst (?f' a t) =
      (\<Sum>b<?n. ?U $$ (a,b) * fst (?f b t)) \<and>
    snd (?f' a t) =
      (\<Sum>b<?n. ?U $$ (a,b) * snd (?f b t))"
    if a: "a < ?n" and t: "t \<in> ?I" for a t
  proof -
    have grid: "fst t \<in> diagonal_grid (cpx_sqrt d) (natural_grid N)"
      using P t by auto
    obtain Q j where tj: "t = (Q,j)" by (cases t) auto
    have Q: "Q \<in> diagonal_grid (cpx_sqrt d) (natural_grid N)"
      using grid tj by simp
    have row: "?f' a t =
      ((\<Sum>b<?n. ?U $$ (a,b) * fst (?f b t)),
       (\<Sum>b<?n. ?U $$ (a,b) * snd (?f b t)))"
      unfolding tj
      by (rule green_transformed_coeff_matrix_row[OF p Q a])
    show ?thesis using row by simp
  qed
  have indexed: "green_gram_determinant d ?I ?f' [0..<?n] =
    green_gram_determinant d ?I ?f [0..<?n]"
  proof (rule green_indexed_gram_determinant_congruence[OF U _ _ det])
    fix a t assume a: "a < ?n" and t: "t \<in> ?I"
    show "fst (?f' a t) = (\<Sum>b<?n. ?U $$ (a,b) * fst (?f b t))"
      using linear[OF a t] by simp
  next
    fix a t assume a: "a < ?n" and t: "t \<in> ?I"
    show "snd (?f' a t) = (\<Sum>b<?n. ?U $$ (a,b) * snd (?f b t))"
      using linear[OF a t] by simp
  qed
  have trans: "green_gram_determinant d ?I ?f' [0..<?n] =
    green_gram_determinant d ?I
      (green_transformed_row_coeff d p S) ?ks"
    using green_gram_determinant_reindex_nth[
      of d ?I "green_transformed_row_coeff d p S" ?ks]
    by simp
  have orig: "green_gram_determinant d ?I ?f [0..<?n] =
    green_row_gram_determinant d P J R S"
    using green_gram_determinant_reindex_nth[
      of d ?I "green_row_gram_coeff d" ?ks]
    by (simp add: green_row_gram_determinant_def)
  show ?thesis using indexed trans orig by simp
qed

lemma (in green_quadratic_character) green_inert_original_paper_determinant_divisible:
  assumes prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
    and P: "P \<subseteq> diagonal_grid (cpx_sqrt d) (natural_grid N)"
  shows "int p ^ (2 * (\<Sum>r<R. \<Sum>s<S.
      min (r div p) (S-1-s))) dvd
    green_row_gram_determinant d P J R S"
proof -
  have ppos: "0 < p" using prime by (simp add: prime_gt_0_nat)
  have eq: "green_gram_determinant d (P \<times> {..<J})
      (green_transformed_row_coeff d p S) (green_row_order R S) =
    green_row_gram_determinant d P J R S"
    by (rule green_inert_gram_determinant_eq[OF ppos P])
  show ?thesis
    using green_inert_transformed_paper_determinant_divisible[
      OF prime odd inert P, where R=R and S=S and J=J]
    by (simp only: eq)
qed

lemma (in green_quadratic_character) green_inert_original_paper_valuation:
  assumes prime: "prime p" and odd: "odd p" and inert: "chi p = -1"
    and P: "P \<subseteq> diagonal_grid (cpx_sqrt d) (natural_grid N)"
    and nonzero: "green_row_gram_determinant d P J R S \<noteq> 0"
  shows "2 * (\<Sum>r<R. \<Sum>s<S. min (r div p) (S-1-s)) \<le>
    multiplicity (int p) (green_row_gram_determinant d P J R S)"
proof -
  have "1 < p" by (rule prime_gt_1_nat[OF prime])
  hence "p \<noteq> 1" by linarith
  hence "\<not> is_unit (int p)" by simp
  have dvd: "int p ^ (2 * (\<Sum>r<R. \<Sum>s<S.
      min (r div p) (S-1-s))) dvd
    green_row_gram_determinant d P J R S"
    by (rule green_inert_original_paper_determinant_divisible[
      OF prime odd inert P])
  show ?thesis
    by (rule multiplicity_geI[OF nonzero \<open>\<not> is_unit (int p)\<close> dvd])
qed

end