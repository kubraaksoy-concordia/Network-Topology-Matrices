section \<open> Matrix and Vector Auxiliary \<close>

theory Matrix_Vector_Auxiliary

imports "Fishers_Inequality.Matrix_Vector_Extras" 
        
begin 

definition sum_abs_vec :: "('a :: {abs, comm_monoid_add}) vec \<Rightarrow> 'a " where
"sum_abs_vec v \<equiv> sum (\<lambda> i . \<bar>v $ i\<bar> ) {0..<dim_vec v}"
lemma sum_absvec_all_zeros[simp]: "sum_abs_vec vNil = 0"
  by (simp add: sum_abs_vec_def)
lemma sum_abs_vec_vCons: "sum_abs_vec (vCons a v) = \<bar>a\<bar> + sum_abs_vec v"
proof -
  have 0: "a = (vCons a v) $ 0"
    by simp 
  have "sum_abs_vec v = sum (\<lambda> i . \<bar> v $ i\<bar>) {0..<dim_vec v}" by (simp add: sum_abs_vec_def)
  also have "... = sum (\<lambda> i . \<bar>(vCons a v) $ Suc i\<bar>) {0..< dim_vec v}"
    by force
  also have "... = sum (\<lambda> i . \<bar>(vCons a v) $ i\<bar>) {Suc 0..< (Suc (dim_vec v))}"
    by (smt (verit) sum.cong sum.shift_bounds_Suc_ivl)  
  finally have sum: "sum_abs_vec v = sum (\<lambda> i .  \<bar>(vCons a v) $ i \<bar>) {Suc 0..< dim_vec (vCons a v)}" by simp
  have "sum_abs_vec (vCons a v) = sum (\<lambda> i .  \<bar>(vCons a v) $ i \<bar>){0..< dim_vec (vCons a v)}" 
    by (simp add: sum_abs_vec_def)
  then have "sum_abs_vec (vCons a v) =  \<bar>(vCons a v) $ 0 \<bar> + sum (\<lambda> i .  \<bar>(vCons a v) $ i \<bar>){Suc 0..< dim_vec (vCons a v)}"
    by (metis dim_vec_vCons sum.atLeast_Suc_lessThan zero_less_Suc) 
  thus ?thesis using sum 0 by simp
qed

lemma sum_abs_vec_vCons_lt: 
  assumes "\<And> i. i < dim_vec (vCons a v) \<Longrightarrow>  \<bar>(vCons a v) $ i\<bar> \<le> (n ::int)"
  assumes "sum_abs_vec v \<le> m"
  shows "sum_abs_vec (vCons a v) \<le> n + m"
  using assms sum_abs_vec_vCons 
  by (metis add.commute add_left_mono dim_vec_vCons_ne_0 dual_order.trans vec_index_vCons_0)

lemma sum_abs_vec_one_zero: 
  assumes "\<And> i. i < dim_vec (v :: int vec) \<Longrightarrow> \<bar>v $ i\<bar> \<le> (1 ::int)"
  shows "sum_abs_vec v \<le> dim_vec v"
  using assms 
  proof (induct v)
    case vNil
    then show ?case by simp
  next
    case (vCons a v)
    then show ?case 
      using sum_abs_vec_vCons_lt 
      by (metis Suc_less_eq dim_vec_vCons of_nat_Suc vec_index_vCons_Suc)
  qed

text \<open>Lemmas related counting occurrences of an element in a vector\<close>
lemma count_abs_vec1_sum_non_zero_elements: 
  fixes v :: "'a :: {field_char_0,idom_abs_sgn} vec"
  assumes nn :  "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 0 \<or> v $ i = 1 \<or> v $ i = (-1)"
  shows "of_nat ((count_vec v 1) + (count_vec v (-1))) = sum_abs_vec v"  
  using assms 
proof(induct v)
  case vNil
  then show ?case
  by (simp add: count_vec_vNil)
next
  case (vCons a v)
  have "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 0 \<or> v $ i = 1 \<or> v $ i = (-1))"
    using vCons.prems by force
  then have IH: "of_nat ((count_vec v 1) + count_vec v (-1)) = sum_abs_vec v"
    using assms vCons.hyps by auto
  have h1: "(\<Sum>i = 0..<dim_vec (vCons a v). \<bar>vCons a v $ i\<bar>) = sum_abs_vec (vCons a v)" 
    by (simp add: sum_abs_vec_def)
   then have h2: "sum (\<lambda>i. \<bar>(vCons a v)$i\<bar>) {0..<dim_vec (vCons a v)} =  \<bar>a\<bar> +  sum_abs_vec (v)"
     by (metis sum_abs_vec_vCons)
   then show ?case 
     using count_vec_vCons dim_vec_vCons_ne_0 sum_abs_vec_vCons vCons.prems vec_index_vCons_0 abs_0 abs_1 abs_minus
     by (smt (verit) IH add.assoc add.commute add_cancel_right_left of_nat_1 of_nat_add one_neq_neg_one)        
 qed

lemma count_abs_vec1_three_elems: 
  fixes v :: "'a :: {idom_abs_sgn, field_char_0} vec"
  assumes "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0 \<or> v $ i = (-1))"
  shows "count_vec v 1 + count_vec v 0 + count_vec v (-1) = dim_vec v"
proof-
 have ss: "vec_set v \<subseteq> {0, 1, -1}" using assms by (auto simp add: vec_set_def)
  have "dim_vec v = size (vec_mset v)"
    by (simp add: mset_vec_same_size) 
  have "size (vec_mset v) = (\<Sum> x \<in> (vec_set v) . count (vec_mset v) x)"
    by (simp add: vec_mset_set size_multiset_overloaded_eq) 
  also have  "... = (\<Sum> x \<in> {0, 1, -1}. count (vec_mset v) x)"
 using size_count_mset_ss ss
  by (metis calculation finite.emptyI finite.insertI vec_mset_set)
  finally have "size (vec_mset v) = count (vec_mset v) 1 + count (vec_mset v) 0 + count (vec_mset v) (-1)" 
    by auto
  thus ?thesis
    by (simp add: mset_vec_same_size)
qed

lemma count_abs_vec1_sum_zeros: 
  fixes v :: "'a :: {idom_abs_sgn, field_char_0} vec"
  assumes "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0 \<or> v $ i = (-1)"
  shows "of_nat (count_vec v 0) = of_nat (dim_vec v) - sum_abs_vec v"
  using count_abs_vec1_three_elems count_abs_vec1_sum_non_zero_elements
  by (smt (verit, ccfv_threshold) add_diff_cancel_left' assms diff_diff_eq2 eq_diff_eq of_nat_add)

lemma sum_abs_vec1_dim_zeros: 
  fixes v :: "'a :: {idom_abs_sgn, field_char_0} vec"
  assumes "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0 \<or> v $ i = (-1)"
  shows " sum_abs_vec v = of_nat (dim_vec v)- of_nat (count_vec v 0)"
  using assms count_abs_vec1_sum_zeros by force

lemma count_abs_vec1_sum_non_zero_elems_alt:
  fixes v :: "'a :: {idom_abs_sgn, field_char_0} vec"
  assumes "vec_set v \<subseteq> {0, 1, -1}"
  shows "of_nat (count_vec v 1 + count_vec v (-1)) = sum_abs_vec v"
proof-
  have "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0 \<or> v $ i = (-1))" 
    using vec_setI assms by auto
  thus ?thesis 
    by (meson count_abs_vec1_sum_non_zero_elements)
qed

lemma count_vec1_sum_non_zero_elems_alt: 
  fixes v :: "'a :: {idom_abs_sgn, field_char_0} vec"
  assumes nn :  "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 0 \<or> v $ i = 1 \<or> v $ i = (-1)"  
shows "of_nat (count_vec v 1)*1 + of_nat (count_vec v (-1)) * (-1) = sum_vec v"
 using assms 
proof(induct v)
  case vNil
  then show ?case
  by (simp add: count_vec_vNil)
next
  case (vCons a v)
  have "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 0 \<or> v $ i = 1 \<or> v $ i = (-1))"
    using vCons.prems nn 
    by (metis Suc_less_eq dim_vec_vCons vec_index_vCons_Suc)
  then have IH: "of_nat (count_vec v 1)*1 + of_nat (count_vec v (-1)) * (-1) = sum_vec v"
    using assms vCons.hyps by auto
  have h1: "(\<Sum>i = 0..<dim_vec (vCons a v). vCons a v $ i) = sum_vec (vCons a v)" 
    by (simp add: sum_vec_def)
   then have h2: "sum (\<lambda>i. (vCons a v)$i) {0..<dim_vec (vCons a v)} =  a +  sum_vec (v)"
     by (metis sum_vec_vCons)
   then show ?case 
     using count_vec_vCons dim_vec_vCons_ne_0 sum_vec_vCons vCons.prems vec_index_vCons_0
     by (smt (verit) IH ab_semigroup_add_class.add_ac(1) add.commute eq_add_iff1 
         ideal.scale_left_distrib minus_mult_commute mult_cancel_left2 
         mult_hom.hom_add of_nat_1 of_nat_add one_neq_neg_one)
 qed

lemma matrl_carrier[simp]:
  "mat_of_rows_list n vs \<in> carrier_mat (length vs) n"
  "dim_row (mat_of_rows_list n vs) = length vs"
  "dim_col (mat_of_rows_list n vs) = n"
  unfolding mat_of_rows_list_def by auto

text\<open>Ported from the existing library @Berlekamp_Type_Based\<close>
lemma row_mat_of_rows_list:
assumes b: "b < length A"
and nc: "\<forall>i. i < length A \<longrightarrow> length (A ! i) = nc"
shows "(row (mat_of_rows_list nc A) b) = vec_of_list (A ! b)"
proof (auto simp add: vec_eq_iff)
  show "nc = length (A ! b)"
    unfolding mat_of_rows_list_def using b nc by auto
  fix i assume i: "i < length (A ! b)"
  show "row (mat_of_rows_list nc A) b $ i = vec_of_list (A ! b) $ i"
    using i b nc
    unfolding mat_of_rows_list_def row_def
    by (transfer, auto simp add: mk_vec_def mk_mat_def)
qed

text \<open>Helpers for the partition of set intervals within the sum\<close>
lemma set_int2: "i \<in> {0..<m::nat} \<longleftrightarrow> i < m"
  by auto
lemma set_int3: "i \<in> {0..<m::nat} \<and> j \<in> {0..<m::nat} \<and> i \<noteq> j \<longrightarrow> j \<in> {0..<m::nat}-{i} "
  by auto
lemma set_int4: "i \<in> {0..<m::nat} \<and> j \<in> {0..<m::nat} \<and> x \<in> {0..<m::nat} \<and> i \<noteq> j \<and> x \<noteq> i \<and> x \<noteq> j\<longrightarrow> x \<in> {0..<m::nat}-{i,j} "
  by auto 
lemma set_int3_disj: 
  assumes "i1 < m" "i2 < m" "i1 \<noteq> i2"
  shows "{0..<m::nat} = ({0..<m} - {i1, i2}) \<union> {i1} \<union> {i2}"
  using assms by auto
lemma two_elem_set: "card {i1,i3} = 2 \<Longrightarrow> i1 \<noteq> i3 "
  by force
lemma sum_disj_2sets:
 assumes "i1 < m" "i3 < m" "i1 \<noteq> i3"
 shows "(\<Sum> i \<in> {0..<m::nat}. f) = (\<Sum> i \<in> ({0..<m} - {i1, i3}). f )+ (\<Sum> i \<in> {i1, i3}. f) "
  using assms set_int3_disj
  by (meson bot.extremum finite_atLeastLessThan insert_subset set_int2 sum.subset_diff)
lemma sum_disj_3sets:
 assumes "i1 < m" "i3 < m" "i1 \<noteq> i3"
 shows "(\<Sum> i \<in> {0..<m::nat}. f )= (\<Sum> i \<in> ({0..<m} - {i1, i3}). f ) + (\<Sum> i \<in> {i1}. f) + (\<Sum> i \<in> {i3}. f)"
proof-
  have a1: "(\<Sum> i \<in> {0..<m::nat}. f )= (\<Sum> i \<in> ({0..<m} - {i1, i3}). f ) +  (\<Sum> i \<in> {i1, i3}. f) "
    using sum_disj_2sets assms by auto
  from this have a2:  "(\<Sum> i \<in> {i1, i3}. f) = (\<Sum> i \<in> {i1, i3} - {i3}. f) +  (\<Sum> i \<in> {i3}. f)"
   using assms(3) by (simp add: insert_Diff_if)
  also have "... = (\<Sum> i \<in> {i1}. f) + (\<Sum> i \<in> {i3}. f)"
    by (simp add: assms(3) insert_Diff_if)
  thus ?thesis using a2 a1 assms 
    by (metis add.assoc)
qed

lemma (in comm_monoid_add) sum_disj_3sets':
 assumes "i1 < m" "i3 < m" "i1 \<noteq> i3"
 shows "(\<Sum> i \<in> {0..<m::nat}. (f :: 'a vec) $ i)= (\<Sum> i \<in> ({0..<m} - {i1, i3}). (f)$ i) + (\<Sum> i \<in> {i1}. f$i) + (\<Sum> i \<in> {i3}. f$i)"
proof-
  have a1: "(\<Sum> i \<in> {0..<m::nat}. f$i )= (\<Sum> i \<in> ({0..<m} - {i1, i3}). f$i ) +  (\<Sum> i \<in> {i1, i3}. f$i) "
    using assms 
    by (meson atLeastLessThan_iff empty_subsetI finite_atLeastLessThan insert_subset less_eq_nat.simps(1) local.sum.subset_diff)
 from this have a2:  "(\<Sum> i \<in> {i1, i3}. f $ i) = (\<Sum> i \<in> {i1, i3} - {i3}. f$i) +  (\<Sum> i \<in> {i3}. f$i)"
   using assms(3) by (simp add: insert_Diff_if)
  also have "... = (\<Sum> i \<in> {i1}. f$i) + (\<Sum> i \<in> {i3}. f$i)"
  by (simp add: assms(3) insert_Diff_if)
  thus ?thesis using a2 a1 assms 
    by (metis add.assoc)
qed

lemma (in idom_abs_sgn) sum_disj_3sets_abs:
 assumes "i1 < m" "i3 < m" "i1 \<noteq> i3"
 shows "(\<Sum> i \<in> {0..<m::nat}. \<bar>(f :: 'a vec) $ i\<bar>)= (\<Sum> i \<in> ({0..<m} - {i1, i3}). \<bar>f$ i\<bar>) + (\<Sum> i \<in> {i1}.\<bar>f$i\<bar>) + (\<Sum> i \<in> {i3}. \<bar>f$i\<bar>)"
proof-
  have a1: "(\<Sum> i \<in> {0..<m::nat}.  \<bar>f$i \<bar> )= (\<Sum> i \<in> ({0..<m} - {i1, i3}). \<bar> f$i \<bar> ) +  (\<Sum> i \<in> {i1, i3}.  \<bar>f$i \<bar>) "
    using assms  by (meson atLeastLessThan_iff empty_subsetI finite_atLeastLessThan insert_subset less_eq_nat.simps(1) local.sum.subset_diff)
 from this have a2:  "(\<Sum> i \<in> {i1, i3}. \<bar>f $ i\<bar>) = (\<Sum> i \<in> {i1, i3} - {i3}. \<bar>f$i\<bar>) +  (\<Sum> i \<in> {i3}.\<bar> f$i\<bar>)"
 using assms(3) by (simp add: insert_Diff_if)
  also have "... = (\<Sum> i \<in> {i1}. \<bar>f$i\<bar>) + (\<Sum> i \<in> {i3}. \<bar>f$i\<bar>)"
 by (simp add: assms(3) insert_Diff_if)
  thus ?thesis using a2 a1 assms 
    by (metis add.assoc)
qed

end
