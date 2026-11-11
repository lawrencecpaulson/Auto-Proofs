theory Row_Coeff_Transform
  imports Inert_Rows
begin

declare [[apply_timeout = 20]]

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

declare [[apply_timeout = 0]]

end
