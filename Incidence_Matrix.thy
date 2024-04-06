theory Incidence_Matrix
  imports Network_Incidence_System         
          "HOL.Relation" 
          "HOL.Set_Interval"         
           Matrix_Vector_Auxiliary
          "QHLProver.Complex_Matrix"
         
begin

text \<open>Enable coercion of nats to reals to assist with reasoning on network properties\<close>
declare [[coercion_enabled]]
declare [[coercion "of_nat :: nat \<Rightarrow> real"]]

subsection \<open>Incidence Vector\<close>

definition incidence_vec :: "'a nodes \<Rightarrow> 'a edge \<Rightarrow> ('b :: {field_char_0} vec)" where
"incidence_vec Ns p \<equiv> vec (length Ns) (\<lambda>i. if (Ns!i) = fst p \<and> (fst p \<noteq> snd p) then 1 else if (Ns!i) = snd p \<and> (fst p \<noteq> snd p) then -1 else 0)"

lemma incidence_vec_elems: "set\<^sub>v (incidence_vec Ns p) \<subseteq> {0, 1, -1}"
by (auto simp add: vec_set_def incidence_vec_def)

lemma finite_neg_inci_vec_elems: "finite (set\<^sub>v (incidence_vec Ns p))"
using finite_subset incidence_vec_elems by blast

lemma incidence_vec_dim: "dim_vec (incidence_vec Ns p) = length Ns" 
  by (simp add: incidence_vec_def)

lemma incidence_vec_index: "i < length Ns \<Longrightarrow> incidence_vec Ns p $ i = (if (fst p \<noteq> snd p) \<and> (Ns!i) = fst p then 1 else if (fst p \<noteq> snd p) \<and> (Ns!i) = snd p then -1 else 0)"
by(simp add: incidence_vec_def)

lemma incidence_vec_index_mone: "i < length Ns \<Longrightarrow> fst p \<noteq> snd p \<Longrightarrow> incidence_vec Ns p $ i = -1 \<longleftrightarrow>  (Ns ! i) = snd p"
  by (simp add: incidence_vec_index)

lemma incidence_vec_index_zero: "i < length Ns \<Longrightarrow>  fst p \<noteq> snd p \<Longrightarrow> incidence_vec Ns p $ i = 0 \<longleftrightarrow> (Ns ! i) \<noteq> snd p \<and> (Ns ! i) \<noteq> fst p"
by(simp add: incidence_vec_def)

lemma incidence_vec_index_zero1: "i < length Ns \<Longrightarrow> (fst p = snd p) \<or> ((Ns ! i) \<noteq> snd p \<and> (Ns ! i) \<noteq> fst p) \<longleftrightarrow> incidence_vec Ns p $ i = 0 "
  unfolding incidence_vec_def by auto

lemma incidence_vec_index_one: "i < length Ns \<Longrightarrow> fst p \<noteq> snd p \<Longrightarrow> incidence_vec Ns p $ i = 1 \<longleftrightarrow>  (Ns ! i) = fst p"
  by(simp add: incidence_vec_def)

subsection \<open>A network represented by a directed graph without self-loops is characterized by an incidence matrix whose entries 0, 1, -1\<close>

definition incidence_matrix :: "'a nodes \<Rightarrow> 'a edges  \<Rightarrow> ('b :: {field_char_0}) mat" where
"incidence_matrix Ns Es \<equiv> mat (length Ns) (length Es) (\<lambda>(i,j). if (fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = fst (Es!j)) then 1  else if (fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = snd (Es!j)) then -1 else 0)"

lemma inci_matcol_dim: "dim_col (incidence_matrix Ns Es) = size Es" 
  by (simp add: incidence_matrix_def)

lemma inci_matrow_dim: "dim_row (incidence_matrix Ns Es) = length Ns"
  by (simp add: incidence_matrix_def)

lemma incidence_mat_elems: "elements_mat (incidence_matrix Ns Es) \<subseteq> {0, 1, -1}"
  by (auto simp add: elements_mat_def incidence_matrix_def)

lemma finite_incidence_mat_elems: "finite (elements_mat (incidence_matrix Ns Es))"
  using finite_subset incidence_mat_elems by blast

lemma incidence_elems_max_3: "card (elements_mat (incidence_matrix Ns Es)) \<le> 3"
  using incidence_mat_elems 
  by (smt (verit, del_insts) card.empty card_insert_if card_mono finite.intros(1) finite.intros(2) le_SucI numeral_3_eq_3)

lemma incidence_index[simp]: "i<length Ns \<Longrightarrow> j < size Es \<Longrightarrow> 
incidence_matrix Ns Es  = mat (length Ns) (length Es) (\<lambda>(i,j). if (fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = fst (Es!j)) then 1  else if (fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = snd (Es!j)) then -1 else 0)"
unfolding incidence_matrix_def by auto

lemma incidence_carrier[simp]: "incidence_matrix Ns Es \<in> carrier_mat (length Ns) (size Es)" 
  unfolding carrier_mat_def by (auto simp add: inci_matcol_dim inci_matrow_dim)

lemma inci_matrix_pos: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = fst (Es!j)
    \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 1"
    unfolding incidence_matrix_def by auto

lemma inci_matrix_neg: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = snd (Es!j)
    \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = -1"
  unfolding incidence_matrix_def by auto    

lemma inci_matrix_0_case1: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) = snd (Es!j))
    \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 0"
  by(simp add: incidence_matrix_def)

lemma inci_matrix_0_case2: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> (Ns!i) \<noteq> fst (Es!j) \<Longrightarrow> (Ns!i) \<noteq> snd (Es!j)
    \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 0"
  using incidence_matrix_def by auto

lemma inci_matrix_mone_neg: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = -1 \<Longrightarrow> 
   (Ns!i) = snd (Es!j)"
  by (metis inci_matrix_0_case2 inci_matrix_pos one_neq_neg_one zero_neq_neg_one)

lemma inci_matrix_one_pos: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 1
    \<Longrightarrow> (Ns!i) = fst (Es!j)"
  by (metis inci_matrix_0_case2 inci_matrix_neg one_neq_neg_one one_neq_zero)

lemma inci_matrix_zero_no_case1: "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 0  \<Longrightarrow>
   (Ns!i) \<noteq> fst (Es!j) \<and>  (Ns!i) \<noteq> snd (Es!j)"
  by (metis inci_matrix_neg inci_matrix_pos zero_neq_neg_one zero_neq_one)

lemma inci_matrix_one_pos_iff:  "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow>  (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> 
    (incidence_matrix Ns Es) $$ (i, j) = 1 \<longleftrightarrow> Ns ! i = fst (Es ! j)"
  using inci_matrix_pos inci_matrix_one_pos by metis

lemma inci_matrix_mone_neg_iff:  "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow>  (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> 
    (incidence_matrix Ns Es) $$ (i, j) = -1 \<longleftrightarrow> Ns ! i = snd (Es ! j)"
  using inci_matrix_neg inci_matrix_mone_neg by auto

lemma inci_matrix_zero_iff1:  "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow>  (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> 
    (incidence_matrix Ns Es) $$ (i, j) = 0 \<longleftrightarrow>  (Ns!i) \<noteq> fst (Es!j) \<and> (Ns!i) \<noteq> snd (Es!j)"
  using inci_matrix_0_case1 inci_matrix_zero_no_case1 by auto

lemma inci_matrix_zero_iff2:  "i < length Ns \<Longrightarrow> j < length Es \<Longrightarrow>  
    (incidence_matrix Ns Es) $$ (i, j) = 0 \<longleftrightarrow>  (fst (Es!j) = snd (Es!j)) \<or> ((fst (Es!j) \<noteq> snd (Es!j)) \<and> (Ns!i) \<noteq> fst (Es!j) \<and> (Ns!i) \<noteq> snd (Es!j))"
  using inci_matrix_0_case1 inci_matrix_zero_no_case1 by auto

lemma inci_matrix_one_implies_snd: "F \<subseteq> {..< length Ns} \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> 
    (\<And> i. i\<in>F \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 1) \<Longrightarrow> i \<in> F \<Longrightarrow> Ns ! i = fst (Es ! j)"
  using inci_matrix_one_pos_iff by blast

lemma inci_matrix_mone_implies_fst: "F \<subseteq> {..< length Ns} \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> 
    (\<And> i. i\<in>F \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = -1) \<Longrightarrow> i \<in> F \<Longrightarrow> Ns ! i = snd (Es ! j)"
  using inci_matrix_mone_neg_iff by blast

lemma inci_matrix_zero_implies_noincident: "F \<subseteq> {..< length Ns} \<Longrightarrow> j < length Es \<Longrightarrow> (fst (Es!j) \<noteq> snd (Es!j)) \<Longrightarrow> 
    (\<And> i. i\<in>F \<Longrightarrow> (incidence_matrix Ns Es) $$ (i, j) = 0) \<Longrightarrow> i \<in> F \<Longrightarrow> Ns ! i \<noteq> fst  (Es ! j) \<and> Ns ! i \<noteq> snd  (Es ! j)"
  using inci_matrix_zero_iff1 by blast

text \<open>Reasoning on Columns/Rows of the incidence matrix\<close>

lemma incidence_matrix_col_def:  "j < length Es \<Longrightarrow> i < length Ns \<Longrightarrow> 
    (col (incidence_matrix Ns Es) j) $ i = (if fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = fst (Es!j) then 1 else if fst (Es!j) \<noteq> snd (Es!j) \<and> (Ns!i) = snd (Es!j) then -1 else 0)"
  by (simp add: incidence_matrix_def)

lemma incidence_mat_col_list_map_elem: "j < length Es \<Longrightarrow> i < length Ns \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow>
    col (incidence_matrix Ns Es) j $ i = map_vec 
    (\<lambda> x . if  (x = fst (Es ! j)) then 1 else if (x = snd (Es ! j)) then -1 else 0) (vec_of_list Ns) $ i"
  by (simp add: incidence_matrix_col_def vec_of_list_index)

lemma inci_mat_col_list_map:  "j < length Es \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow>
    col (incidence_matrix Ns Es) j = map_vec (\<lambda> x . if (x = fst (Es ! j)) then 1 else if (x = snd (Es ! j)) then -1 else 0) (vec_of_list Ns)"
 by (intro eq_vecI,
    simp_all add: inci_matcol_dim inci_matrow_dim incidence_mat_col_list_map_elem index_vec_of_list incidence_matrix_def)

lemma incidence_matrix_row_def:  "j < length Es \<Longrightarrow> i < length Ns \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow>
    (row (incidence_matrix Ns Es) i) $ j = (if (Ns!i) = fst (Es!j) then 1 else if (Ns!i) = snd (Es!j) then -1 else 0)"
  by (simp add: incidence_matrix_def)

lemma incidence_matrix_row_list_map_elem: "j < length Es \<Longrightarrow> i < length Ns \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow>
    row (incidence_matrix Ns Es) i $ j = map_vec (\<lambda> b . if ((Ns ! i) = fst b) then 1 else if ((Ns ! i) = snd b) then -1 else 0) (vec_of_list Es) $ j"
  by(simp add: incidence_matrix_def vec_of_list_index)

lemma inci_mat_row_list_map:  "i < length Ns \<Longrightarrow> 
    row (incidence_matrix Ns Es) i = map_vec (\<lambda> b . if  (fst b \<noteq> snd b) \<and> (Ns ! i)= fst b then 1 else if (fst b \<noteq> snd b) \<and> (Ns ! i)= snd b then -1 else 0) (vec_of_list Es)"
 by (smt (z3) dim_vec_of_list eq_vecI inci_matcol_dim inci_matrix_0_case1 inci_matrow_dim incidence_matrix_row_def index_map_vec(1) index_map_vec(2) index_row(1) index_row(2) index_vec_of_list)

text \<open>Connection between incidence vector and incidence matrix\<close>

lemma incidence_mat_inci_colvec: "j < length Es \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow> col (incidence_matrix Ns Es) j = incidence_vec Ns (Es ! j)"
  by (auto simp add: incidence_matrix_def incidence_vec_def)

lemma inc_mat_of_cols_inc_vecs: 
  assumes "\<forall>j \<in> {0..< length Es}. fst (Es!j) \<noteq> snd (Es!j)"
  shows "cols (incidence_matrix Ns Es) = map (\<lambda> j . incidence_vec Ns j) Es"
proof (intro nth_equalityI)
  have l1: "length (cols (incidence_matrix Ns Es)) = length Es"
    using inci_matcol_dim by simp
  have l2: "length (map (\<lambda> j . incidence_vec Ns j) Es) = length Es"
    using length_map by simp
  then show "length (cols (incidence_matrix Ns Es)) = length (map (incidence_vec Ns) Es)" 
    using l1 l2 by simp
  show "\<And>i. i < length (cols (incidence_matrix Ns Es)) \<Longrightarrow> cols (incidence_matrix Ns Es) ! i = map (incidence_vec Ns) Es ! i "
    using incidence_mat_inci_colvec l1 
    by (metis assms atLeastLessThan_iff cols_length cols_nth linorder_not_le not_less_zero nth_map)
qed

text \<open>Network system properties for the incidence matrices\<close>

text\<open>For all columns of the incidence matrix, there are two non zero elements which are 1 and -1\<close>
definition nempty_col :: "('a :: {field_char_0}) mat \<Rightarrow> nat \<Rightarrow> bool" where
"nempty_col A j \<equiv> \<exists> x y. x \<noteq> 0 \<and> y \<noteq> 0 \<and> x \<noteq> y \<and> x \<in>$ col A j \<and> y \<in>$ col A j"

text\<open>Characterization for indicating the number of 1's and (-1)'s in the row and column of the incidence matrix\<close>

definition mat_in_degree_num :: "('a :: {field_char_0}) mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_in_degree_num A i  \<equiv> count_vec (row A i) (-1)"

definition mat_out_degree_num :: "('a :: {field_char_0}) mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_out_degree_num A i  \<equiv> count_vec (row A i) (1)"

definition mat_degree_num :: "'a :: {field_char_0} mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_degree_num A i  \<equiv> mat_in_degree_num A i + mat_out_degree_num A i"

definition zeros_in_row :: "'a :: {field_char_0} mat \<Rightarrow> nat \<Rightarrow> nat" where
"zeros_in_row A i  \<equiv>  count_vec (row A i) 0"

definition mat_outedge_num :: "'a :: {field_char_0} mat \<Rightarrow> nat \<Rightarrow> nat" where 
"mat_outedge_num A j \<equiv> count_vec (col A j) (1)"

definition mat_inedge_num :: "'a :: {field_char_0} mat \<Rightarrow> nat \<Rightarrow> nat" where 
"mat_inedge_num A j \<equiv> count_vec (col A j) (-1)"

definition mat_col_size :: "('a :: {field_char_0}) mat \<Rightarrow> nat \<Rightarrow> nat" where 
"mat_col_size A j \<equiv> mat_outedge_num A j + mat_inedge_num A j"

text\<open>We define a column's size of a incidence matrix  as the number of non zero entry in the column. 
The @mat_col_size_sum_alt lemma shows that the size of a column equals to the absolute sum of its elements\<close>
lemma mat_col_size_sum_alt: 
  fixes A :: "'a :: {field_char_0, idom_abs_sgn} mat"
  shows "elements_mat A \<subseteq> {0, 1, -1} \<Longrightarrow> j < dim_col A 
                              \<Longrightarrow> of_nat (mat_col_size A j) = sum_abs_vec (col A j)"
  unfolding mat_col_size_def mat_outedge_num_def mat_inedge_num_def
  using count_abs_vec1_sum_non_zero_elems_alt col_elems_subset_mat subset_trans
  by metis

lemma mat_degree_property: 
  fixes A :: "'a :: {field_char_0, idom_abs_sgn} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "i < dim_row A \<Longrightarrow> of_nat (mat_degree_num A i) = sum_abs_vec (row A i)"
  unfolding mat_degree_num_def mat_in_degree_num_def  mat_out_degree_num_def
   using row_elems_subset_mat subset_trans 
   by (metis (no_types, lifting) add.commute assms count_abs_vec1_sum_non_zero_elems_alt)

lemma mat_zeros: 
  fixes A :: "'a :: {field_char_0, idom_abs_sgn} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}" 
  shows "i < dim_row A \<Longrightarrow> zeros_in_row A i = card {j. j < dim_col A \<and> A $$ (i,j) = 0}"
  using assms zeros_in_row_def count_vec_alt row_def
  by (smt (verit) Collect_cong index_row(1) index_row(2))

lemma A_elems_simp:
  fixes A :: "'a :: {field_char_0} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> A $$ (i, j) = 0 \<or>  A $$ (i, j) = 1 \<or> A $$ (i, j) = -1"
  using assms by auto

lemma mat_nonzeros: 
  fixes A :: "'a :: {field_char_0, idom_abs_sgn} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}" 
  shows "i < dim_row A \<Longrightarrow> (mat_degree_num A i) = dim_col A - zeros_in_row A i"
  unfolding mat_degree_num_def mat_in_degree_num_def  mat_out_degree_num_def zeros_in_row_def
proof-
  assume ii:  "i < dim_row A"
  then show "count_vec (row A i) (- 1) + count_vec (row A i) 1 = dim_col A - count_vec (row A i) 0 "
  proof-
    have a1: "dim_vec (row A i) = dim_col A"
      using assms ii by force
    have 1 :"of_nat (count_vec (row A i) 1) + of_nat (count_vec (row A i) (-1)) = sum_abs_vec (row A i)"
      using assms ii count_abs_vec1_sum_non_zero_elems_alt
      by (metis (no_types, lifting)  of_nat_add row_elems_subset_mat subset_trans)
    also have "... = of_nat (dim_col A) - of_nat (count_vec (row A i) 0)"
      using sum_abs_vec1_dim_zeros assms ii a1 
      by (metis A_elems_simp index_row(1))
    thus ?thesis using zeros_in_row_def 1 a1 assms 
      by (metis add.commute of_nat_add of_nat_diff of_nat_eq_iff vec_count_lt_dim)
  qed
qed

lemma A_not_zero_simp:
  fixes A :: "'a :: {field_char_0} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> A $$ (i, j) \<noteq> 0 \<Longrightarrow> A $$ (i, j) = 1 \<or> A $$ (i, j) = -1"
  using assms by auto

lemma A_not_zero_one_simp: 
  fixes A :: "'a :: {field_char_0} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> i < dim_row A \<Longrightarrow> A $$ (i, j) \<noteq> 0 \<Longrightarrow> A $$ (i, j) \<noteq> 1 \<Longrightarrow> A $$ (i, j) = -1"
  using assms by auto

lemma A_not_mone_zero_simp: 
fixes A :: "'a :: {field_char_0} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> A $$ (i, j) \<noteq> 0 \<Longrightarrow> A $$ (i, j) \<noteq> -1 \<Longrightarrow> A $$ (i, j) = 1"
  using assms by blast

lemma A_not_mone_one_simp: 
  fixes A :: "'a :: {field_char_0} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> A $$ (i, j) \<noteq> 1 \<Longrightarrow> A $$ (i, j) \<noteq> -1 \<Longrightarrow> A $$ (i, j) = 0"
  using assms by blast

lemma A_index_square_abs_itself:
  fixes A :: "'a :: {field_char_0,idom_abs_sgn} mat"
  assumes ee: "elements_mat A \<subseteq> {0, 1, -1}"
  shows"i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> (A $$ (i, j))^2 = abs (A $$ (i, j))"
  using assms  by fastforce
  
lemma A_row_index_square_abs_itself:
 fixes A :: "'a :: {field_char_0,idom_abs_sgn} mat"
 assumes "elements_mat A \<subseteq> {0, 1, -1}"
 shows "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> ((row A i) $ j) ^ 2 = abs ((row A i) $ j)"
  using A_index_square_abs_itself assms by auto

lemma A_col_index_square_abs_itself:
 fixes A :: "'a :: {field_char_0,idom_abs_sgn} mat"
 assumes "elements_mat A \<subseteq> {0, 1, -1}"
 shows "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> ((col A j) $ i) ^ 2 = abs ((col A j) $ i)"
  using A_index_square_abs_itself assms by auto

text \<open>Alternate way of degree representing by product of row matrices\<close>

lemma scalar_prod_inc_vec_degree_num_mat:
   fixes A :: "'a :: {field_char_0,idom_abs_sgn} mat"
   assumes "i < dim_row A"
   assumes ee :"elements_mat A \<subseteq> {0, 1, -1}"
  shows "(row A i) \<bullet> (row A i) = of_nat (mat_degree_num A i)"
proof-
  have "(row A i) \<bullet> (row A i) = (\<Sum> j \<in> {0..<dim_col A} . (row A i) $ j * (row A i) $ j)" 
    using assms scalar_prod_def sum.cong 
     by (metis (no_types, lifting) index_row(2))
   also have "... = (\<Sum> j \<in> {0..<dim_col A} . ((row A i) $ j)^2)"
     by (metis power2_eq_square)
   also have "... = (\<Sum> j \<in> {0..<dim_col A} . abs ((row A i) $ j))"
    using A_row_index_square_abs_itself 
    by (metis (no_types, lifting) assms(1) ee sum.ivl_cong)
  finally show ?thesis using sum_abs_vec_def mat_degree_property ee assms(1)
    by (metis index_row(2))
qed

lemma scalar_prod_inc_vec_col_mat:
   fixes A :: "'a :: {field_char_0,idom_abs_sgn} mat"
   assumes "j < dim_col A"
   assumes ee :"elements_mat A \<subseteq> {0, 1, -1}"
  shows "(col A j) \<bullet> (col A j) = of_nat (mat_col_size A j)"
proof-
  have "(col A j) \<bullet> (col A j) = (\<Sum> i \<in> {0..<dim_row A}. (col A j) $ i * (col A j) $ i)" 
    using assms scalar_prod_def sum.cong 
    by (smt (verit) dim_col)
   also have "... = (\<Sum> i \<in> {0..<dim_row A}. ((col A j) $ i)^2)"
     by (metis power2_eq_square)
   also have "... = (\<Sum> i \<in> {0..<dim_row A}. abs ((col A j) $ i))"
     by (meson A_col_index_square_abs_itself assms sum.ivl_cong)     
   finally show ?thesis using sum_abs_vec_def ee assms(1)
     by (metis dim_col mat_col_size_sum_alt)
qed

text \<open>Degree representing by product of incidence matrix and its transpose\<close>
lemma mat_degree_alt: 
  fixes A :: "'a :: {field_char_0, idom_abs_sgn} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "i < dim_row A \<Longrightarrow> of_nat (mat_degree_num A i) = (A * (transpose_mat A)) $$ (i,i)"
proof-
  assume row: "i < dim_row A " 
  then have 1:  "of_nat (mat_degree_num A i) = (row A i) \<bullet> (row A i)"
    using  assms scalar_prod_inc_vec_degree_num_mat by metis
  also have "... = (A * (transpose_mat A)) $$ (i,i)"
  using times_mat_def transpose_mat_def by (simp add: row)
  thus ?thesis using 1 by auto
qed

text \<open>Summation of degrees of all nodes representing by trace of the product of incidence matrix and its transpose\<close>
lemma trace_degree: 
fixes A :: "'a :: {field_char_0, idom_abs_sgn} mat"
  assumes "elements_mat A \<subseteq> {0, 1, -1}"
  shows "(\<Sum> i \<in> {..< dim_row A}. of_nat (mat_degree_num A i)) = trace ((A * (transpose_mat A)))"
proof-
 have "dim_row (A * (transpose_mat A)) = dim_row A"
    by simp_all
  thus ?thesis 
  unfolding trace_def using assms mat_degree_alt  
  by (metis (no_types, lifting) atLeast0LessThan lessThan_iff sum.cong)
qed

text \<open>nonzero column obtains in terms of index\<close>
lemma nempty_col_obtains:
  assumes "nempty_col A j" 
  obtains i1 i2  where "i1 < dim_row A" and "i2 < dim_row A" and "i1 \<noteq> i2"
                              and "(col A j) $ i1 \<noteq> 0 \<and> (col A j) $ i2 \<noteq> 0"
proof -
  have d: "dim_vec (col A j) = dim_row A" by simp
  obtain x y where "x \<noteq> 0" and "y \<noteq> 0" and "x \<noteq> y" "x \<in>$ col A j" "y \<in>$ col A j" 
    using assms by (auto simp add: nempty_col_def) 
  thus ?thesis using vec_contains_obtains_index d
    by (metis that) 
qed

text \<open>Alternate way to represent in- and out-degree via indexes cardinality\<close>
lemma mat_out_deg_num_alt:  
  assumes "i < dim_row A"
  shows "mat_out_degree_num A i = card {j . j < dim_col A \<and> A $$ (i, j) = 1}"
proof(simp add: mat_out_degree_num_def)
  have eq: "\<And>j. (j < dim_col A \<and> A$$(i,j) = 1) = (row A i $ j = 1 \<and> j < dim_vec (row A i))"
    using assms by auto
  have "count_vec (row A i) 1 = card {j. (row A i) $ j = 1 \<and>  j < dim_vec (row A i)}"
     using count_vec_alt[of "row A i" "1"] by simp
 thus "count_vec (row A i) 1 = card {j. j < dim_col A \<and> A $$ (i, j) = 1}"
   using eq Collect_cong by simp
qed

lemma mat_in_deg_num_alt:  
  assumes "i < dim_row A"
  shows "mat_in_degree_num A i = card {j . j < dim_col A \<and> A $$ (i, j) = -1}"
proof(simp add: mat_in_degree_num_def)
  have eq: "\<And>j. (j < dim_col A \<and> A$$(i,j) = -1) = (row A i $ j = -1 \<and> j < dim_vec (row A i))"
    using assms by auto
  have "count_vec (row A i) (-1) = card {j. (row A i) $ j = -1 \<and> j < dim_vec (row A i)}"
     using count_vec_alt[of "row A i" "(-1)"] by simp
 thus "count_vec (row A i) (-1) = card {j. j < dim_col A \<and> A $$ (i, j) = -1}"
   using eq Collect_cong by simp
qed

lemma mat_degree_index_alt:
  fixes A :: "'a :: {field_char_0, idom_abs_sgn} mat"
  assumes "i < dim_row A"
  shows  "mat_degree_num A i = card {j . j < dim_col A \<and> A $$ (i, j) = -1} + card {j . j < dim_col A \<and> A $$ (i, j) = 1} "
  unfolding mat_degree_num_def using mat_in_deg_num_alt mat_out_deg_num_alt 
  using assms by fastforce


context nonempty_network_system
begin 

text\<open>Uniqness of the incidence vectors and matrices\<close>
lemma incidence_vec_eq_iff_edges: 
  assumes "e1 \<in> \<E>"
  assumes "e2 \<in> \<E>"
  shows "incidence_vec \<N>s e1 = incidence_vec \<N>s e2  \<longleftrightarrow> e1 = e2"
proof(intro iffI eq_vecI, simp_all add: incidence_vec_dim assms)
  define v1 :: "'c :: {field_char_0} vec" where "v1 = incidence_vec \<N>s e1"
  define v2 :: "'c :: {field_char_0} vec" where "v2 = incidence_vec \<N>s e2"
  assume a: "v1 = v2"
  then have "dim_vec v1 = dim_vec v2"
    by (simp add: incidence_vec_dim) 
   then have "\<And> i. i < dim_vec v1 \<Longrightarrow> v1 $ i = v2 $ i" using a by simp
   then have "\<And> i. i < length \<N>s \<Longrightarrow> v1 $ i = v2 $ i" by (simp add: v1_def incidence_vec_dim)
   then have a1: "\<And> i. i < length \<N>s \<Longrightarrow> (\<N>s ! i) = fst e1  \<longleftrightarrow> (\<N>s ! i) = fst e2 "
     using incidence_vec_index_one v1_def v2_def by (metis assms no_self_loop)
   then have a2: "\<And> i. i < length \<N>s \<Longrightarrow> (\<N>s ! i) = snd e1  \<longleftrightarrow> (\<N>s ! i) = snd e2 "
     using incidence_vec_index_mone v1_def v2_def  no_self_loop by (metis a assms)
   then have a3: "\<And> x. x \<in> \<N> \<Longrightarrow> fst e1 = x  \<longleftrightarrow> fst e2 = x "
       using valid_nodes_index_cons 
       by (metis a1)
   then have a4: "\<And> y. y \<in> \<N> \<Longrightarrow> snd e1 = y  \<longleftrightarrow> snd e2 = y "
    using valid_nodes_index_cons
    by (metis a2)
   then show "e1 = e2" 
     using assms network_wf 
     by (simp add: a3 a4 prod_eq_iff)
 qed

lemma incidence_mat_eq_imp_edges_list: 
  assumes "nonempty_network_system \<N>s \<E>s" "nonempty_network_system \<N>s \<K>s"
  shows "incidence_matrix \<N>s \<E>s = incidence_matrix \<N>s \<K>s  \<longrightarrow>  \<E>s = \<K>s"
proof
  define mat1 :: "'c :: {field_char_0} mat" where "mat1 = incidence_matrix \<N>s \<E>s"
  define mat2 :: "'c :: {field_char_0} mat" where "mat2 = incidence_matrix \<N>s \<K>s"
  assume a: "mat1 = mat2"
  then have "dim_col mat1 = dim_col mat2" "dim_row mat1 = dim_row mat2"
      by (auto simp add: inci_matrow_dim inci_matcol_dim) 
  then have a1: "\<And> i j. i < dim_row mat1 \<and> j < dim_col mat1 \<Longrightarrow> mat1 $$(i,j) = mat2 $$ (i,j)" 
      using a by simp
  then have a2: "\<And> i j . i < length \<N>s  \<and> j < length  \<E>s \<Longrightarrow> mat1 $$(i,j) = mat2 $$ (i,j)"
    by (simp add: mat1_def inci_matrow_dim inci_matcol_dim)
  have "\<And>x. x \<in> set \<K>s \<Longrightarrow> fst x \<in> \<N> \<and> snd x \<in> \<N> \<and> fst x \<noteq> snd x "
  using assms(2) finite_netw_sys.axioms(1) network_system.network_wf nonempty_network_system.axioms(1) by blast
  then have a3: "\<And> i j . i < length \<N>s \<and> j < length \<E>s \<Longrightarrow> (\<N>s ! i) = fst (\<E>s!j) \<longleftrightarrow> (\<N>s ! i) = fst (\<K>s!j)"
    using assms a  inci_matcol_dim inci_matrix_one_pos_iff mat1_def mat2_def
    by (metis exists_nodes nonempty_network_system.valid_edges_index)   
   then have a4: "\<And> i j . i < length \<N>s \<and> j < length \<E>s \<Longrightarrow> (\<N>s ! i) = snd (\<E>s!j) \<longleftrightarrow> (\<N>s ! i) = snd (\<K>s!j)"
    using inci_matrix_mone_neg no_self_loop  mat1_def mat2_def 
    by (smt (verit, best) a inci_matcol_dim inci_matrix_zero_iff2)
   then have "\<And> x j. x \<in> \<N> \<and> j <  length \<E>s \<Longrightarrow>  x = fst (\<E>s!j) \<longleftrightarrow> x = fst (\<K>s!j)"
     by (metis a3 valid_nodes_index_cons)
  then have "\<And> x y j. y \<in> \<N>-{x} \<and> j < length \<E>s \<Longrightarrow>  y = snd (\<E>s!j) \<longleftrightarrow> y = snd (\<K>s!j)"
    using a4 valid_nodes_index_cons by (metis DiffD1)
  then show "\<E>s = \<K>s"
    using assms network_wf a a3 a4 inci_matcol_dim mat1_def mat2_def
    by (smt (verit, ccfv_threshold) edges_valid_nodes_index1 fst_conv nth_equalityI prod.exhaust_sel snd_conv)
qed

lemma uniqueness_incidence_mat: 
  assumes "nonempty_network_system \<N>s \<E>s" "nonempty_network_system \<N>s \<K>s"
  shows "incidence_matrix \<N>s \<E>s = incidence_matrix \<N>s \<K>s  \<longleftrightarrow>  \<E>s = \<K>s"
proof
  show  "incidence_matrix \<N>s \<E>s = incidence_matrix \<N>s \<K>s \<Longrightarrow> \<E>s = \<K>s"
    using assms incidence_mat_eq_imp_edges_list by auto
next
  let ?mat1 = "incidence_matrix \<N>s \<E>s" 
  let ?mat2 = "incidence_matrix \<N>s \<K>s"
  assume b: "\<E>s = \<K>s" 
  then have "length \<E>s = length \<K>s" by auto
  then have "dim_col ?mat1 = dim_col ?mat2"  "dim_row ?mat1 = dim_row ?mat2"
    by (auto simp add: inci_matrow_dim inci_matcol_dim) 
  then have a1: "\<And> i j. i < dim_row ?mat1 \<and> j < dim_col ?mat1 \<Longrightarrow> ?mat1 $$(i,j) = ?mat2 $$ (i,j)" 
    using b by fastforce
  then show "?mat1 = ?mat2"
    using b  by fastforce
qed


abbreviation K :: "real mat" where
"K \<equiv> incidence_matrix \<N>s \<E>s"

lemma K_alt_def:"K = mat m n (\<lambda> (i,j). if pos_incident (\<N>s!i) (\<E>s!j) then 1 else if neg_incident (\<N>s!i) (\<E>s!j) then -1 else 0)"
  unfolding incidence_matrix_def using neg_incident_netw_altdef pos_incident_netw_altdef wf_network_system wf_network_system_iff by auto

lemma pos_inc_K_one: "i < dim_row K \<Longrightarrow> j < dim_col K \<Longrightarrow> pos_incident (\<N>s!i) (\<E>s!j) \<Longrightarrow> K $$ (i,j) = 1"
  using K_alt_def pos_incident_netw_altdef by fastforce

lemma neg_inc_K_mone: "i < dim_row K \<Longrightarrow> j < dim_col K \<Longrightarrow> neg_incident (\<N>s!i) (\<E>s!j) \<Longrightarrow> K $$ (i,j) = -1"
  using K_alt_def neg_incident_netw_altdef neg_not_pos_incident by auto

lemma no_inc_K_zero: "i < dim_row K \<Longrightarrow> j < dim_col K \<Longrightarrow> \<not> neg_incident (\<N>s!i) (\<E>s!j) \<Longrightarrow> \<not> pos_incident (\<N>s!i) (\<E>s!j) \<Longrightarrow> K $$ (i,j) = 0"
  by (simp add: K_alt_def)

text \<open>Basic properties on ordered lists \<close>

lemma nodes_indexing: "\<N>s \<in> permutations_of_set \<N>"
  by (simp add: permutations_of_set_def distincts)

lemma edges_indexing: "\<E>s \<in> permutations_of_set \<E>"
  by (simp add: permutations_of_set_def distincts)

text \<open>Matrix Dimension related lemmas \<close>
 
lemma K_carrier_mat: "K \<in> carrier_mat m n" 
  by (simp add: incidence_matrix_def)

lemma dim_row_K[simp]: "dim_row K = m"
  using inci_matrow_dim by auto

lemma dim_col_K[simp]: "dim_col K = n"
  using inci_matcol_dim by auto 

lemma dim_vec_row_K: "dim_vec (row K i) = n"
  by simp

lemma dim_vec_col_K: "dim_vec (col K i) = m" by simp 

lemma dim_vec_K_col: 
  assumes "j < n"
  shows "dim_vec (cols K ! j) = m"
  by (simp add: assms incidence_vec_dim)

lemma K_elems: "elements_mat (K) \<subseteq> {0, 1, -1}"
  by (auto simp add: incidence_matrix_def elements_mat_def)

lemma K_elems_max_3: "card (elements_mat K) \<le> 3"
  using K_elems numeral_3_eq_3
  by (smt (verit, del_insts) card.empty card_insert_if card_mono finite.intros(1) finite.intros(2) le_SucI numeral_3_eq_3)

text \<open>Transpose properties \<close>

lemma transpose_K_mult_dim: "dim_row (K * K\<^sup>T) = m" "dim_col (K * K\<^sup>T) = m"
  by (simp_all)

lemma K_trans_index_val: "i < dim_col K \<Longrightarrow> j < dim_row K \<Longrightarrow> 
    K\<^sup>T $$ (i, j) = (if pos_incident (\<N>s!j) (\<E>s!i) then 1 else if 
 neg_incident (\<N>s!j) (\<E>s!i) then -1 else 0)"
  using K_alt_def by simp

lemma transpose_entries: "elements_mat (K\<^sup>T) \<subseteq> {0, 1, -1}"
  by (metis K_elems transpose_mat_elems)
 
text \<open>Matrix element and index related lemmas \<close>

lemma K_mat_row_elems: "i < m \<Longrightarrow> vec_set (row K i) \<subseteq> {0, 1, -1}"
  by (metis K_elems dim_row_K row_elems_subset_mat subset_trans)

lemma K_mat_col_elems: "j < n \<Longrightarrow> vec_set (col K j) \<subseteq> {0, 1, -1}"
  by (metis K_elems col_elems_subset_mat dim_col_K subset_trans)

lemma K_matrix_elems_one_mone_zero: "i < m \<Longrightarrow> j < n \<Longrightarrow> K $$ (i, j) = 0 \<or> K $$ (i, j) = 1 \<or> K $$ (i, j) = -1" 
  by (simp add: incidence_matrix_def)

lemma K_not_zero_simp: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> K $$ (i, j) \<noteq> 0 \<Longrightarrow> K $$ (i, j) = 1 \<or> K $$ (i, j) = -1"
  using incidence_mat_elems[of "\<N>s" "\<E>s"]
  by (smt (verit, best) dim_col_K dim_row_K incidence_matrix_col_def index_col)

lemma K_not_one_simp: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> K $$ (i, j) \<noteq> 1 \<Longrightarrow> K $$ (i, j) = 0 \<or> K $$ (i, j) = -1"
  using incidence_mat_elems
  by (smt (verit, best) dim_col_K dim_row_K incidence_matrix_col_def index_col)

lemma K_not_mone_simp: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> K $$ (i, j) \<noteq> -1 \<Longrightarrow> K $$ (i, j) = 0 \<or> K $$ (i, j) = 1"
  using incidence_mat_elems
  by (smt (verit, best) dim_col_K dim_row_K incidence_matrix_col_def index_col)

lemma K_not_Mone_simp: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> K $$ (i, j) \<noteq> 1 \<Longrightarrow> K $$ (i, j) \<noteq> -1 \<Longrightarrow> K $$ (i, j) = 0"
  using K_not_mone_simp by blast

lemma K_not_zeromone_simp: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> K $$ (i, j) \<noteq> 0 \<Longrightarrow> K $$ (i, j) \<noteq> -1 \<Longrightarrow> K $$ (i, j) = 1"
  using K_elems K_matrix_elems_one_mone_zero by blast

lemma K_ge0[simp]: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> K $$ (i, j) > 0 \<Longrightarrow>  K $$ (i, j) = 1"
  using K_elems K_matrix_elems_one_mone_zero 
  by (smt (verit) dim_col_K dim_row_K)

lemma K_le0[simp]: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> K $$ (i, j) < 0 \<Longrightarrow>  K $$ (i, j) = -1"
  using K_elems K_matrix_elems_one_mone_zero 
  by (smt (verit) dim_col_K dim_row_K)

lemma K_matrix_pos_iff: "i < m \<Longrightarrow> j < n \<Longrightarrow> K $$ (i, j) = 1 \<longleftrightarrow> \<N>s!i = fst (\<E>s!j) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j)"
  using inci_matrix_one_pos_iff no_self_loop valid_edges_index by blast

lemma K_matrix_neg_iff: "i < m \<Longrightarrow> j < n \<Longrightarrow>  K $$ (i, j) = -1 \<longleftrightarrow> \<N>s !i = snd (\<E>s!j) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) "
  using inci_matrix_mone_neg_iff by (metis wf_network_system_iff nth_mem wf_network_system)

lemma K_matrix_zero_iff: "i < m \<Longrightarrow> j < n \<Longrightarrow> fst (\<E>s!j)  \<noteq> snd (\<E>s!j) \<Longrightarrow> K $$ (i, j) = 0 \<longleftrightarrow> \<N>s !i \<noteq> fst (\<E>s!j) \<and> \<N>s !i \<noteq> snd (\<E>s!j)"
  by (meson in_set_conv_nth inci_matrix_zero_iff1 network_wf)

lemma K_matrix_zero_iff2: "i < m \<Longrightarrow> j < n \<Longrightarrow> K $$ (i, j) = 0 \<longleftrightarrow> fst (\<E>s!j) = snd (\<E>s!j) \<or> (\<N>s !i \<noteq> fst (\<E>s!j) \<and> \<N>s !i \<noteq> snd (\<E>s!j))"
  using  K_matrix_zero_iff by auto

lemma K_index_square_itself: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> (K $$ (i, j))^2 = abs (K $$ (i, j))"
  using K_not_zero_simp by fastforce

text \<open>Incidence Matrix rows/columns related lemmas \<close>

lemma K_row_index_square_itself: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> ((row K i) $ j)^2 = abs ((row K i) $ j)"
  using index_row  K_index_square_itself by auto 

lemma K_col_index_square_itself: "j < dim_col K \<Longrightarrow> i < dim_row K \<Longrightarrow> ((col K j) $ i)^2 = abs ((col K j) $ i)"
  by simp

lemma K_col_def_conv_pos: "j < n \<Longrightarrow> i < m \<Longrightarrow> (col K j) $ i = 1 \<Longrightarrow> (\<N>s!i) = fst (\<E>s!j) \<and>  fst (\<E>s!j) \<noteq> snd (\<E>s!j)\<Longrightarrow> (pos_incident (\<N>s!i) (\<E>s!j))"
  using pos_incident_cond_indexed by blast

lemma K_col_def_conv_mone: "j < n \<Longrightarrow> i < m \<Longrightarrow> (col K j) $ i = -1 \<Longrightarrow> (\<N>s!i) = snd (\<E>s!j) \<and>  fst (\<E>s!j) \<noteq> snd (\<E>s!j)"
proof -
  assume a1: "col K j $ i = - 1"
  assume a2: "i < m"
  assume a3: "j < n"
  then have "\<E>s ! j \<in> \<E>"
    using nth_mem by blast
  then have "network_system \<N>s \<E>s \<and> \<E>s ! j \<in> \<E>"
    using wf_network_system by force
  then have "fst (\<E>s ! j) \<noteq> snd (\<E>s ! j)"
    using network_system.network_wf by blast
  then show ?thesis
    using a3 a2 a1
    by (metis incidence_mat_inci_colvec incidence_vec_index_mone)
qed

text \<open>Incidence Vector's of Incidence Matrix columns \<close>

lemma col_incidence_vec: "j < length \<E>s \<Longrightarrow> incidence_vec \<N>s (\<E>s ! j) = col K j"
  by (metis incidence_mat_inci_colvec network_system.network_wf nth_mem wf_network_system)

text \<open>Incidence matrix column properties\<close>

lemma K_col_def: "j < n \<Longrightarrow> i < m \<Longrightarrow> (col K j) $ i = (if (\<N>s!i) = fst (\<E>s!j) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then 1 else if (\<N>s!i) = snd (\<E>s!j)  \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then -1 else 0)"
  using incidence_matrix_col_def network_wf
  by (simp add: network_wf)

lemma K_col_def_indiv: 
     "j < n \<Longrightarrow> i < m \<Longrightarrow> fst (\<E>s!j) \<noteq> snd (\<E>s!j) \<Longrightarrow> (\<N>s!i) = fst (\<E>s!j) \<Longrightarrow> (col K j) $ i = 1"
     "j < n \<Longrightarrow> i < m  \<Longrightarrow> fst (\<E>s!j) \<noteq> snd (\<E>s!j) \<Longrightarrow> (\<N>s!i) = snd (\<E>s!j) \<Longrightarrow> (col K j) $ i = -1"
     "j < n \<Longrightarrow> i < m \<Longrightarrow> (\<N>s!i) \<noteq> fst (\<E>s!j) \<Longrightarrow>  (\<N>s!i) \<noteq> snd (\<E>s!j) \<Longrightarrow> (col K j) $ i = 0"
  using K_col_def by auto

lemma K_col_list_map_elem: "j < n \<Longrightarrow> i < m  \<Longrightarrow> 
    col K j $ i = map_vec (\<lambda> x . if (x = fst (\<E>s ! j)) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then 1 else if (x = snd (\<E>s ! j)) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then -1 else 0) (vec_of_list \<N>s) $ i"
  using no_self_loop nth_mem by (simp add: vec_of_list_index)

lemma K_col_list_map: "j < n \<Longrightarrow> col K j = map_vec (\<lambda> x . if (x =fst (\<E>s ! j)) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then 1 else  if (x = snd (\<E>s ! j)) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then -1 else 0) (vec_of_list \<N>s)"
  using K_col_list_map_elem by (simp add: vec_eq_iff)

lemma K_row_def: "j < n \<Longrightarrow> i < m \<Longrightarrow> (row K i) $ j = (if (\<N>s!i) = fst (\<E>s!j) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then 1 else if (\<N>s!i) = snd (\<E>s!j)  \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then -1 else 0)"
 using incidence_matrix_row_def by (simp add: network_wf)

lemma K_row_def_indiv: 
     "j < n \<Longrightarrow> i < m \<Longrightarrow> fst (\<E>s!j) \<noteq> snd (\<E>s!j) \<Longrightarrow> (\<N>s!i) = fst (\<E>s!j) \<Longrightarrow> (row K i) $ j = 1"
     "j < n \<Longrightarrow> i < m  \<Longrightarrow> fst (\<E>s!j) \<noteq> snd (\<E>s!j) \<Longrightarrow> (\<N>s!i) = snd (\<E>s!j) \<Longrightarrow> (row K i) $ j = -1"
     "j < n \<Longrightarrow> i < m \<Longrightarrow> (\<N>s!i) \<noteq> fst (\<E>s!j) \<Longrightarrow>  (\<N>s!i) \<noteq> snd (\<E>s!j) \<Longrightarrow> (row K i) $ j = 0"
  by(simp_all add: K_matrix_pos_iff K_matrix_zero_iff K_matrix_neg_iff)

lemma K_row_list_map_elem: "j < n \<Longrightarrow> i < m  \<Longrightarrow> 
    row K i $ j = map_vec (\<lambda> y . if ((\<N>s!i) = fst y) \<and> fst y \<noteq> snd y then 1 else if ((\<N>s!i) = snd y) \<and> fst y \<noteq> snd y then -1 else 0) (vec_of_list \<E>s) $ j"
  using no_self_loop nth_mem by (simp add: vec_of_list_index)

lemma K_row_list_map: "i < m \<Longrightarrow> 
  row K i = map_vec (\<lambda> y . if ((\<N>s!i) = fst y) \<and> fst y \<noteq> snd y then 1 else if ((\<N>s!i) = snd y) \<and> fst y \<noteq> snd y then -1 else 0) (vec_of_list \<E>s)"
  using K_row_list_map_elem by (simp add: vec_eq_iff)


text\<open>The whole columns of the matrix K are distinct\<close>

lemma distinct_cols_K: "distinct (cols K)"
proof-
  have "inj_on (\<lambda> e. incidence_vec \<N>s e) (\<E>)"
     by (simp add: incidence_vec_eq_iff_edges inj_on_def) 
   then show ?thesis
     using distinct_map distincts(2) inc_mat_of_cols_inc_vecs 
     by (smt (verit, best) col_incidence_vec cols_length cols_nth dim_col_K 
          distinct_conv_nth incidence_vec_eq_iff_edges nth_mem)
qed

lemma incidence_vec_map_col_vec: "j < n \<Longrightarrow> incidence_vec \<N>s (\<E>s ! j) = (map_vec (\<lambda> x . if (x =fst (\<E>s ! j)) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then 1 else  if (x = snd (\<E>s ! j)) \<and> fst (\<E>s!j) \<noteq> snd (\<E>s!j) then -1 else 0) (vec_of_list \<N>s) ::real vec)"
  using col_incidence_vec K_col_list_map by auto
   
text \<open>Alternate positive - negative oriented edge representations \<close>

lemma pos_edges_mat_cond_rep:
  assumes "j < length \<E>s" and "fst (\<E>s ! j) \<noteq> snd (\<E>s ! j)"
  shows " fst (\<E>s ! j) \<in> ((!) \<N>s) ` { i. i < length \<N>s \<and> K $$ (i, j) = 1}"
  by (smt (verit, best) K_matrix_pos_iff assms imageI mem_Collect_eq nth_mem 
           valid_nodes_index_obtains wf_network_system wf_network_system_iff)

lemma neg_edges_mat_cond_rep:
  assumes "j < length \<E>s" and "fst (\<E>s ! j) \<noteq> snd (\<E>s ! j)"
  shows "snd (\<E>s ! j) \<in> ((!) \<N>s)`{ i. i < length \<N>s \<and> K $$ (i, j) = -1}"
  by (smt (verit, best) K_matrix_neg_iff assms imageI mem_Collect_eq nth_mem valid_nodes_index_obtains
           wf_network_system wf_network_system_iff)

lemma no_incidence_edge_mat_cond_rep:
 assumes "j < length \<E>s" and "fst (\<E>s ! j) \<noteq> snd (\<E>s ! j)"
 shows "fst (\<E>s ! j) \<notin> ((!) \<N>s) ` { i. i < length \<N>s \<and> K $$ (i, j) = 0}" 
       "snd (\<E>s ! j) \<notin> ((!) \<N>s) ` { i. i < length \<N>s \<and> K $$ (i, j) = 0}"
proof-
  show "fst (\<E>s ! j) \<notin> (!) \<N>s ` {i. i < m \<and> K $$ (i, j) = 0}"
    using assms K_matrix_zero_iff wf_network_system by fastforce
  show "snd (\<E>s ! j) \<notin> (!) \<N>s ` {i. i < m \<and> K $$ (i, j) = 0} "
    using K_matrix_neg_iff assms by force
qed

text\<open>mat_degree of K is found by absolute summation of each row elements\<close>
lemma mat_degree_num_K_row: 
  assumes "i < m"
  shows "mat_degree_num K i = sum_abs_vec (row K i)"
  by (simp add: K_elems assms mat_degree_property)

text\<open>Trace version for mat_degree of K\<close>

lemma mat_degree_trace:
  shows "i < dim_row K \<Longrightarrow> (mat_degree_num K i) = (K * (transpose_mat K)) $$ (i,i)"
  by (simp add: K_elems mat_degree_alt)

lemma trace_degree_K: 
  shows "(\<Sum> i \<in> {..< m}. (mat_degree_num K i)) = trace ((K * (transpose_mat K)))"
  using K_elems trace_degree[of K] by simp

lemma mat_row_elem: "i < m \<Longrightarrow> j < n \<Longrightarrow> K $$ (i,j) = row K i $ j"
  using row_def by auto

lemma mat_col_elem: "i < m \<Longrightarrow> j < n \<Longrightarrow> K $$ (i,j) = col K j $ i"
  using col_def by auto

lemma Kpos_fst_exist: "\<forall>j\<in>{0..<n}. \<exists>i \<in> {0..<m}. fst (\<E>s!j) = \<N>s !i \<longleftrightarrow>  K$$(i,j) = 1" 
  using network_wf edges_outdeg_index 
  by (metis K_matrix_pos_iff lessThan_atLeast0 lessThan_iff valid_edges_index)

lemma Kneg_snd_exist: "\<forall>j\<in>{..<n}. \<exists>i \<in> {..<m}. snd (\<E>s!j) = \<N>s !i \<longleftrightarrow>  K$$(i,j) = -1" 
  using network_wf edges_indeg_index 
  by (metis K_matrix_neg_iff lessThan_iff valid_edges_index)

lemma Knoposneg_zero_exist: "\<forall>j\<in>{..<n}. \<exists>i \<in> {..<m}. fst (\<E>s!j) \<noteq>  \<N>s !i \<and> snd (\<E>s!j) \<noteq> \<N>s !i \<longleftrightarrow> K$$(i,j) = 0" 
  using network_wf K_matrix_zero_iff lessThan_iff valid_edges_index
  by (metis in_set_conv_nth)

lemma K_alt_fst: "i < m \<Longrightarrow> {j. j < dim_col K \<and> K$$(i,j) = 1} = {j. \<N>s !i = fst (\<E>s!j) \<and> j < dim_col K}"
  by (metis (no_types, lifting) K_matrix_pos_iff dim_col_K exists_nodes valid_edges_index)

lemma K_alt_snd: "i < m \<Longrightarrow> {j. j < dim_col K \<and> K$$(i,j) =-1} = {j. \<N>s !i = snd (\<E>s!j) \<and> j < dim_col K}"
  by (metis (no_types, lifting) K_matrix_neg_iff dim_col_K exists_nodes valid_edges_index)

lemma mat_neg_alt:"(\<Union>i\<in>{0..<m}. ({j. j < n \<and> K$$(i,j) = -1})) = {j. j<n}"
proof
  show "(\<Union>i\<in>{0..<m}. {j. j < n \<and> K$$(i,j) = -1}) \<subseteq> {j. j < n}"
  proof
    fix x assume xx: "x \<in> (\<Union>i\<in>{0..<m}. {j. j < n \<and> K$$(i,j) = -1})"
    then show "x \<in> {j. j < n}"
    proof
      fix k assume i: "k \<in> {0..<m}" and " x \<in> {j. j < n \<and> K$$(k,j) = -1}"
      then have "K$$(k,x) = -1"  by auto    
      thus ?thesis using xx by auto
    qed
  qed
  show "{j. j < n} \<subseteq> (\<Union>i\<in>{0..<m}. {j. j < n \<and> K $$ (i, j) = - 1})"
  proof
    fix x assume x2: "x \<in> {j. j < n}"
    then show "x \<in> (\<Union>i\<in>{0..<m}. {j. j < n \<and> K $$ (i, j) = - 1})"
    proof          
     obtain ia where i1: "ia \<in> {0..<m}" "\<N>s !ia = snd (\<E>s!x) " 
         using m_non_zero neg_snd_exist 
          by (smt (verit, best) mem_Collect_eq nodes_set_index valid_edges_index x2)
      then have  "x \<in> {j. K $$ (ia, j) = - 1  \<and> j < n}"
          using neg_inc_K_mone wf_nonempty_netw_list_sys x2 by fastforce   
        thus ?thesis using i1 x2 
          by blast
      qed
    qed
  qed

lemma card_mat_neg: "card (\<Union>i\<in>{0..<m}. ({j. j < n \<and> K $$ (i, j) = - 1})) = n"
  using mat_neg_alt card_Collect_less_nat by auto

lemma card_mat_neg_sum: "card (\<Union>i\<in>{0..<m}. ({j. j < n \<and> K $$ (i, j) = - 1})) = (\<Sum>i\<in>{0..<m}. mat_in_degree_num K i)"
proof-
  define I where "I = {0..<m}"
 then have 1: "finite I" by simp
 then have 2:"\<forall>i\<in>I. finite ({j. j < n \<and> K $$ (i, j) = - 1})" by auto
 then have 3: "\<forall>i\<in>I.\<forall>k\<in>I. i\<noteq>k \<longrightarrow> {j. j < n \<and> K $$ (i, j) = - 1} \<inter> {j. j < n \<and> K $$ (k, j) = - 1} = {}"
   using I_def K_matrix_neg_iff distinct_node_index 
   by (smt (verit, ccfv_threshold) Int_emptyI lessThan_atLeast0 lessThan_iff mem_Collect_eq)
 then have "card (\<Union>i\<in>{0..<m}. ({j. j < n \<and> K $$ (i, j) = - 1})) = (\<Sum>i\<in>I. card {j. j < n \<and> K$$(i,j) = -1})"
   using 1 2 I_def card_UN_disjoint  by (metis (no_types, lifting) sum.cong)    
 then have "card (\<Union>i\<in>{0..<m}. ({j. j < n \<and> K $$ (i, j) = - 1})) = (\<Sum>i\<in>{0..<m}. mat_in_degree_num K i)"
   by(simp add: mat_in_deg_num_alt I_def)
  thus ?thesis by auto
qed

text\<open>The sum of in-degree of all nodes equals to the number of edges\<close>
lemma card_mat_neg_sum_n: "(\<Sum>i\<in>{0..<m}. mat_in_degree_num K i) = dim_col K"
  using card_mat_neg card_mat_neg_sum by auto

lemma mat_indeg_neginc_num: "(\<Sum>i\<in>{0..<m}. mat_in_degree_num K i) = (\<Sum>i\<in>{0..<m}. (neginc_num (\<N>s ! i)))"
  using mat_indeg_eq_sumdeg_index_n card_mat_neg_sum_n by auto

lemma mat_pos_alt:"(\<Union>i\<in>{0..<m}. ({j. j < n \<and> K$$(i,j) = 1})) = {j. j<n}"
proof
  show "(\<Union>i\<in>{0..<m}. {j. j < n \<and> K$$(i,j) = 1}) \<subseteq> {j. j < n}"
  proof
    fix x assume xx: "x \<in> (\<Union>i\<in>{0..<m}. {j. j < n \<and> K$$(i,j) = 1})"
    then show "x \<in> {j. j < n}"
    proof
      fix k assume i: "k \<in> {0..<m}" and " x \<in> {j. j < n \<and> K$$(k,j) = 1}"
      then have "K$$(k,x) = 1"  by auto    
      thus ?thesis using xx by auto
    qed
  qed
  show "{j. j < n} \<subseteq> (\<Union>i\<in>{0..<m}. {j. j < n \<and> K $$ (i, j) = 1})"
  proof
    fix x assume x2: "x \<in> {j. j < n}"
    then show "x \<in> (\<Union>i\<in>{0..<m}. {j. j < n \<and> K $$ (i, j) = 1})"
    proof          
     obtain ia where i1: "ia \<in> {0..<m}" "\<N>s !ia = fst (\<E>s!x) " 
         using m_non_zero pos_fst_exist 
          by (smt (verit, best) mem_Collect_eq nodes_set_index valid_edges_index x2)
      then have  "x \<in> {j.  j < n \<and> K $$ (ia, j) = 1}"
          using pos_inc_K_one wf_nonempty_netw_list_sys x2 by fastforce   
        thus ?thesis using i1 x2 
          by blast
      qed
    qed
  qed

lemma card_mat_pos: "card (\<Union>i\<in>{0..<m}. ({j. j < n \<and> K $$ (i, j) = 1})) = n"
  using mat_pos_alt card_Collect_less_nat by auto

lemma card_mat_posneg_sum: "card (\<Union>i\<in>{0..<m}. ({j. j < n \<and> K $$ (i, j) = - 1})) = card (\<Union>i\<in>{0..<m}. ({j. j < n \<and> K $$ (i, j) = 1}))"
  using card_mat_neg card_mat_pos by auto

lemma card_mat_pos_sum: "card (\<Union>i\<in>{0..<m}. ({j. j < n \<and> K $$ (i, j) = 1})) = (\<Sum>i\<in>{0..<m}. mat_out_degree_num K i)"
proof-
  define I where "I = {0..<m}"
 then have 1: "finite I" by simp
 then have 2:"\<forall>i\<in>I. finite ({j. j < n \<and> K $$ (i, j) = 1})" by auto
 then have 3: "\<forall>i\<in>I.\<forall>k\<in>I. i\<noteq>k \<longrightarrow> {j. j < n \<and> K $$ (i, j) = 1} \<inter> {j. j < n \<and> K $$ (k, j) = 1} = {}"
   using I_def K_matrix_pos_iff distinct_node_index 
   by (smt (verit, ccfv_threshold) Int_emptyI lessThan_atLeast0 lessThan_iff mem_Collect_eq)
 then have "card (\<Union>i\<in>{0..<m}. ({j. j < n \<and> K $$ (i, j) = 1})) = (\<Sum>i\<in>I. card {j. j < n \<and> K$$(i,j) =1})"
   using 1 2 I_def card_UN_disjoint  by (metis (no_types, lifting) sum.cong)    
 then have "card (\<Union>i\<in>{0..<m}. ({j. j < n \<and> K $$ (i, j) = 1})) = (\<Sum>i\<in>{0..<m}. mat_out_degree_num K i)"
   by(simp add: mat_out_deg_num_alt I_def)
  thus ?thesis by auto
qed

text\<open>The sum of out-degree of all nodes equals to the number of edges\<close>
lemma card_mat_pos_sum_n: "(\<Sum>i\<in>{0..<m}. mat_out_degree_num K i) = dim_col K"
  using card_mat_pos card_mat_pos_sum dim_col_K by auto

lemma mat_outdeg_posinc_num: "(\<Sum>i\<in>{0..<m}. mat_out_degree_num K i) = (\<Sum>i\<in>{0..<m}. (posinc_num (\<N>s ! i)))"
  using  card_mat_pos_sum_n mat_outdeg_eq_sumdeg_index_n by auto

text\<open>The sum of degree of all nodes equals to twice the number of edges\<close>
lemma inci_sumalldegree_2n:
  shows "(\<Sum>i\<in>{0..<m}. mat_degree_num K i) = 2 * (dim_col K)"
  using card_mat_pos_sum_n card_mat_neg_sum_n mat_degree_num_def[of K _] 
  by (simp add: atLeast0LessThan)

text\<open>Algebraic version of the Handshaking lemma which states the sum of degree of all nodes is twice the number of edges\<close>
lemma trace_degree_2n:
  shows "trace ((K * (transpose_mat K))) = 2 * (dim_col K)"
proof-
  have "trace ((K * (transpose_mat K))) = (\<Sum> i \<in> {..< dim_row K}. (mat_degree_num K i))"
    using trace_degree_K mat_degree_num_def by auto
  thus ?thesis using inci_sumalldegree_2n     
   lessThan_atLeast0 trace_degree_K by presburger
qed

text\<open>Existence of nonzero entries of K\<close>  
lemma nempty_entries_K_col:  
  assumes "j < dim_col K" 
  shows "nempty_col K j \<longleftrightarrow> (\<exists> i1 i2 . i1 < dim_row K \<and> i2 < dim_row K \<and> i1 \<noteq> i2 \<and> K $$ (i1, j) \<noteq> 0 \<and> K $$ (i2, j) \<noteq> 0)"
proof-
  have a1: "nempty_col K j \<Longrightarrow> \<exists>i1 i2. i1 < dim_row K \<and> i2 < dim_row K \<and> i1 \<noteq> i2 \<and> K $$ (i1, j) \<noteq> 0 \<and> K $$ (i2, j) \<noteq> 0"
   using index_col assms by (metis nempty_col_obtains)
  then have "\<exists>i1 i2. i1 < dim_row K \<and> i2 < dim_row K \<and> i1 \<noteq> i2 \<and> K $$ (i1, j) \<noteq> 0 \<and> K $$ (i2, j) \<noteq> 0 \<Longrightarrow> nempty_col K j "
  proof-
  assume a1: "\<exists>i1 i2. i1 < dim_row K \<and> i2 < dim_row K \<and> i1 \<noteq> i2 \<and> K $$ (i1, j) \<noteq> 0 \<and> K $$ (i2, j) \<noteq> 0"    
  from a1  obtain i1 i2 where ne: "i1 \<noteq> i2" and ii: "i1 < dim_row K" "i2 < dim_row K" and nii: " K $$ (i1, j) \<noteq> 0"  "K $$ (i2, j) \<noteq> 0" 
    by blast
  then have 1: "i1 < dim_vec (col K j)" "i2 < dim_vec (col K j)" by simp+
  then have "col K j $ i1 \<noteq> 0" "col K j $ i2 \<noteq> 0" "i1 \<noteq> i2" using nii assms ne by auto
  then obtain x y where "x \<noteq> 0" "y \<noteq> 0" "x \<noteq> y" "col K j $ i1 = x" "col K j $ i2 = y" 
    using 1 assms dim_col_K dim_row_K
    by (metis K_matrix_zero_iff2 ii inci_matrix_mone_neg_iff index_col distinct_node_index)
   thus ?thesis using nempty_col_def 1 assms by (metis vec_setI)   
 qed
  thus ?thesis using a1 assms by auto
qed  

lemma K_mat_nempty_elist: 
  assumes "j < n"
  shows "1 \<in>$ (col K j) \<and> (-1) \<in>$ (col K j)"
proof-
  obtain e where edge: "\<E>s!j = e" by simp
  then have "e \<in> \<E>" using assms valid_edges_index by blast
  then obtain x y where oute: "fst e = x" and ine: "snd e = y" and "x \<noteq> y"
    using edges_nempty exists_nodes by presburger
  then obtain i1 i2 where indx: "\<N>s ! i1 = x" and indx: "\<N>s ! i2 = y" and indim: "i1 < m" "i2 < m" 
    using edges_indeg_index valid_nodes_index_cons by (metis \<open>e \<in> \<E>\<close> edges_valid_nodes_index)
  then have "K $$ (i1,j) = 1 \<and> K $$ (i2,j) = -1"  
    using edge ine \<open>e \<in> \<E>\<close> oute network_wf indim by (metis assms inci_matrix_pos inci_matrix_neg)
  thus ?thesis using vec_setI 
    by (metis assms dim_col_K dim_row_K dim_vec_col_K index_col indim)
qed

lemma all_cols_nempty: "j < n \<Longrightarrow> nempty_col K j"
  using edges_nempty 
  by (smt (verit, best) K_mat_nempty_elist nempty_col_def)

lemma case_1_mat:  assumes "i < length \<N>s" and "j < length \<E>s" 
  shows "fst (\<E>s!j) = \<N>s!i \<Longrightarrow> col (incidence_matrix \<N>s \<E>s) j $ i = 1"
  unfolding col_def incidence_matrix_def using assms case_1
  by fastforce

lemma case_m1_mat:  assumes "i < length \<N>s" and "j < length \<E>s " 
  shows "snd (\<E>s!j) = \<N>s!i \<Longrightarrow> col (incidence_matrix \<N>s \<E>s) j $ i = -1"
  unfolding col_def incidence_matrix_def using assms case_1
  by fastforce

text\<open>The sum of all rows of K is zero\<close> 
lemma allrow_sum_0:  
  shows "(\<Sum>i\<in>{0..<m}. sum_vec (row (K::real mat) i)) = 0"
proof-    
  have "(\<Sum>i\<in>{0..<m}. sum_vec (row K i)) = (\<Sum>i\<in>{0..<m}. of_nat (mat_out_degree_num K i) + (-of_nat (mat_in_degree_num K i)))"
   proof-
  have 1: "(\<Sum>i\<in>{0..<m}. sum_vec (row K i)) = (\<Sum>i\<in>{0..<m}. of_nat (count_vec (row K i) 1)*1 + of_nat (count_vec (row K i) (-1)) * (-1))"
    using count_vec1_sum_non_zero_elems_alt
    by (smt (verit, ccfv_SIG) K_row_def dim_vec_row_K set_int2 sum.cong wf_nonempty_netw_list_sys) 
  also have "... = (\<Sum>i\<in>{0..<m}. (mat_out_degree_num K i) + (mat_in_degree_num K i) * (-1))" 
    by(simp add: mat_out_degree_num_def mat_in_degree_num_def)
  also have "... =  (\<Sum>i\<in>{0..<m}. (mat_out_degree_num K i) + (-(mat_in_degree_num K i)))"
    using mult_minus1_right by auto
  finally show ?thesis using 1 by auto
  qed
  also have "... = (\<Sum>i\<in>{0..<m}. of_nat (mat_out_degree_num K i)) + (\<Sum>i\<in>{0..<m}. (-of_nat (mat_in_degree_num K i)))"
    using sum.distrib[of "\<lambda>i. real (mat_out_degree_num K i)""\<lambda>i. -real (mat_in_degree_num K i)" "{0..<m}"] by blast 
  also have "... = (\<Sum>i\<in>{0..<m}. of_nat (mat_out_degree_num K i))-(\<Sum>i\<in>{0..<m}. of_nat (mat_in_degree_num K i))" 
    using sum_negf by fastforce
  also have "... = dim_col K - dim_col K"  
  using  card_mat_pos_sum_n card_mat_neg_sum_n 
  by (metis diff_self diff_self_eq_0 of_nat_0 of_nat_sum)
  finally show ?thesis by simp
qed

text\<open>The sum of a column's elements of K is zero\<close>
lemma column_elem_sum_0: 
  assumes dim: "j < n"  "i < m" "i1 < m" "i3 < m" "i1 \<noteq> i3"   
  assumes gen:  "fst (\<E>s!j) = \<N>s!i1" "snd (\<E>s!j) = \<N>s!i3" 
                "\<forall>x \<in> ({0..<m} - {i1,i3}). (\<N>s!x \<noteq> fst (\<E>s!j)) \<and> (\<N>s!x \<noteq> snd (\<E>s!j))"
  shows "sum_vec (col (K::real mat) j) = 0"
proof-  
   have 0: "\<And>j. j < n  \<longrightarrow> fst (\<E>s!j) \<noteq> snd (\<E>s!j)"
      using network_wf by auto
   obtain i1 where 1: "fst (\<E>s!j) = \<N>s!i1" "i1<m"  
      using dim(3) gen(1) dim(1) by blast
   obtain i3 where 2: "i1 \<noteq> i3" "snd (\<E>s!j) = \<N>s!i3" "i3 < m" 
      by (metis "1"(1) dim(3) dim(4) dim(5) gen(1) gen(2))
  have a1: "fst (\<E>s!j) = \<N>s!i1 \<longleftrightarrow> (col (K::real mat) j) $ i1 = 1" 
    using dim(1) dim(3) gen(1) K_col_def_indiv(1) edges_nempty 1 case_1_mat by blast   
  have a2: "snd (\<E>s!j) = \<N>s!i3 \<longleftrightarrow> (col (K::real mat) j) $ i3 = -1" 
      using assms K_col_def_indiv(2) 2 edges_nempty  by (metis "0")
  have a3: "(\<forall>x \<in> ({0..<m} - {i1,i3}). (col (K::real mat) j) $ x = 0)"  
  proof-   
    have "\<forall>x \<in> ({0..<m} - {i1,i3}). (col (K::real mat) j) $ x \<noteq> 1 \<and> (col (K::real mat) j) $ x \<noteq> -1" 
     using assms a1 0 a2 edges_nempty 
     by (metis "1"(1) "1"(2) "2"(2) "2"(3) DiffD1 K_col_def_indiv(3) distinct_node_index set_int2 zero_neq_neg_one zero_neq_one)
   then show "(\<forall>x \<in> ({0..<m} - {i1,i3}). (col (K::real mat) j) $ x = 0)"  
     using  K_not_Mone_simp assms
     by (metis (mono_tags, opaque_lifting) Diff_iff K_matrix_elems_one_mone_zero atLeastLessThan_iff mat_col_elem)
 qed
  have d1: "sum_vec (col (K::real mat) j) =  (\<Sum> i \<in> {0..<m}. (col (K::real mat) j) $ i)"
      by(simp add: sum_vec_def)
  also have d2:  "... = (\<Sum> i \<in> {0..<m}-{i1, i3}. (col (K::real mat) j) $ i ) + 
           (\<Sum> i \<in> {i1}.  (col (K::real mat) j) $ i) + 
              (\<Sum> i \<in> {i3}.  (col (K::real mat) j) $ i)"
    using assms sum_disj_3sets' "1"(2) "2"(1) "2"(3) by blast
  also have "... = 0" 
    using  a1 a2 a3 assms 
    by (smt (verit) "1"(1) "2"(2) Diff_empty Diff_iff finite.intros(1) sum.insert sum.not_neutral_contains_not_neutral)
  finally show  ?thesis using assms d1 by presburger
qed

lemma sum_columns_0: "j < n \<Longrightarrow> sum_vec (col (K::real mat) j) = 0"
  using column_elem_sum_0 
  by (smt (verit, del_insts) Diff_iff distinct_node_index edges_valid_nodes_index insert_iff set_int2 valid_edges_index)

text\<open>The sum of the elements of all columns of K is zero\<close>
lemma allsum_columns_0:   
  shows "(\<Sum>j< n. sum_vec (col (K::real mat) j)) = 0"
  using sum_columns_0 by simp

lemma sum_cols_count_eqs: "j < n \<Longrightarrow> of_nat (mat_outedge_num K j) = of_nat (mat_inedge_num K j)"
  unfolding mat_outedge_num_def mat_inedge_num_def
proof-
  assume j: "j < n "
  then show "of_nat (count_vec (col K j) 1) = of_nat (count_vec (col K j) (- 1))" 
  proof-
  have sv0: "sum_vec (col (K::real mat) j) = of_nat 0" using sum_columns_0 j by auto
  have a1: "sum_vec (col (K::real mat) j) 
        = of_nat (count_vec (col (K::real mat) j) 1)*1 + of_nat (count_vec  (col (K::real mat) j) (-1)) * (-1)"  
    using count_vec1_sum_non_zero_elems_alt j 
    by (metis dim_vec_col_K nonempty_network_system.K_col_def wf_nonempty_netw_list_sys)
  also have "... = of_nat (count_vec (col (K::real mat) j) 1) - of_nat (count_vec  (col (K::real mat) j) (-1))"
    by auto
  then have "sum_vec (col (K::real mat) j) = of_nat (count_vec (col (K::real mat) j) 1) - of_nat (count_vec  (col (K::real mat) j) (-1))" 
    using a1 by auto
  then have "(0::real) = of_nat (count_vec (col (K::real mat) j) 1) - of_nat (count_vec  (col (K::real mat) j) (-1))"
    using sv0 by auto
  then have " of_nat (count_vec (col (K::real mat) j) 1) = of_nat (count_vec  (col (K::real mat) j) (-1))"
    by auto   
  thus ?thesis by auto
qed
qed

text\<open>The absolute sum of a column's elements of K is two\<close>
lemma column_elem_abssum_2: 
  assumes dim: "j < n"  "i < m" "i1 < m" "i3 < m" "i1 \<noteq> i3" 
  assumes gen:  "fst (\<E>s!j) = \<N>s!i1" "snd (\<E>s!j) = \<N>s!i3" 
                "\<forall>x \<in> ({0..<m} - {i1,i3}). (\<N>s!x \<noteq> fst (\<E>s!j)) \<and> (\<N>s!x \<noteq> snd (\<E>s!j))"
  shows "sum_abs_vec (col (K::real mat) j) = 2"
proof-  
   have 0: "\<And>j. j < n  \<longrightarrow> fst (\<E>s!j) \<noteq> snd (\<E>s!j)"
      using network_wf by auto
   obtain i1 where 1: "fst (\<E>s!j) = \<N>s!i1" "i1<m"
      using dim(3) gen(1) dim(1) by blast
   obtain i3 where 2: "i1 \<noteq> i3" "snd (\<E>s!j) = \<N>s!i3" "i3 < m" 
      by (metis "1"(1) dim(3) dim(4) dim(5) gen(1) gen(2))
  have a1: "fst (\<E>s!j) = \<N>s!i1 \<longleftrightarrow> (col (K::real mat) j) $ i1 = 1" 
    using dim(1) dim(3) gen(1) K_col_def_indiv(1) edges_nempty 1 case_1_mat by blast   
  have a2: "snd (\<E>s!j) = \<N>s!i3 \<longleftrightarrow> (col (K::real mat) j) $ i3 = -1" 
      using assms K_col_def_indiv(2) 2 edges_nempty  by (metis "0")
  have a3: "(\<forall>x \<in> ({0..<m} - {i1,i3}). (col (K::real mat) j) $ x = 0)"  
  proof-   
    have "\<forall>x \<in> ({0..<m} - {i1,i3}). (col (K::real mat) j) $ x \<noteq> 1 \<and> (col (K::real mat) j) $ x \<noteq> -1" 
     using assms a1 0 a2 edges_nempty 
     by (metis "1"(1) "1"(2) "2"(2) "2"(3) DiffD1 K_col_def_indiv(3) distinct_node_index set_int2 zero_neq_neg_one zero_neq_one)
   then show "(\<forall>x \<in> ({0..<m} - {i1,i3}). (col (K::real mat) j) $ x = 0)"  
     using  K_not_Mone_simp assms
     by (metis (mono_tags, opaque_lifting) Diff_iff K_matrix_elems_one_mone_zero atLeastLessThan_iff mat_col_elem)
 qed
  have d1: "sum_abs_vec (col (K::real mat) j) =  (\<Sum> i \<in> {0..<m}. \<bar>(col (K::real mat) j) $ i\<bar>)"
      by(simp add: sum_abs_vec_def)
  also have d2:  "... = (\<Sum> i \<in> {0..<m}-{i1, i3}. \<bar>(col (K::real mat) j) $ i\<bar>) + 
           (\<Sum> i \<in> {i1}. \<bar>(col (K::real mat) j) $ i\<bar> ) + 
              (\<Sum> i \<in> {i3}. \<bar>(col (K::real mat) j) $ i\<bar>)"
    using assms sum_disj_3sets_abs "1"(2) "2"(1) "2"(3) by blast
  also have "... = 2" 
    using  a1 a2 a3 assms 
    by (smt (verit) "1"(1) "2"(2) Diff_empty Diff_iff finite.intros(1) sum.insert sum.not_neutral_contains_not_neutral)
  finally show  ?thesis using assms d1 by presburger
qed

text\<open>Generalized version of @column_elem_abssum_2\<close>
lemma sum_incicol_elem_2: "j < n \<Longrightarrow> sum_abs_vec (col (K::real mat) j) = 2"
  using column_elem_abssum_2
  by (smt (verit, del_insts) Diff_iff distinct_node_index edges_valid_nodes_index insert_iff set_int2 valid_edges_index)

text\<open>All columns' absolute summation is equal to twice the number of edges\<close>
lemma allsum_columns_2n:   
  shows "(\<Sum>j< n. sum_abs_vec (col (K::real mat) j)) = 2 * n"
proof-
  have "(\<Sum>j< n. sum_abs_vec (col (K::real mat) j)) = (\<Sum>j\<in>{0..<n}. 2)"
    using sum_incicol_elem_2 by simp
  thus ?thesis by auto
qed

text\<open>Every column of incidence matrix has only one 1\<close>
lemma incicol_has_one_1: "j < n \<Longrightarrow> (mat_outedge_num K j) = 1"
proof-
  assume j: "j < n"
  have a1: "sum_abs_vec (col (K::real mat) j) = of_nat 2"
    using j sum_incicol_elem_2 by auto
  also have "... = of_nat ((count_vec (col (K::real mat) j) 1) + (count_vec (col (K::real mat) j) (-1)))"
    using count_abs_vec1_sum_non_zero_elems_alt K_elems j 
    by (metis K_mat_col_elems calculation) 
  also have "... = of_nat (count_vec (col (K::real mat) j) 1) + of_nat (count_vec (col (K::real mat) j) 1)"
     using sum_cols_count_eqs 
     by (metis j mat_inedge_num_def mat_outedge_num_def of_nat_add)
  finally  have "real 2 = 2 * of_nat (mat_outedge_num K j)"
    using a1 mat_outedge_num_def 
    by (smt (verit, best) j mult_2 of_nat_1 of_nat_1_eq_iff one_add_one sum_incicol_elem_2)
  thus ?thesis by auto
qed

text\<open>Every column of incidence matrix has only one -1\<close>
lemma incicol_has_one_m1: "j < n \<Longrightarrow> (mat_inedge_num K j) = 1"
  unfolding mat_inedge_num_def 
  by (metis incicol_has_one_1 mat_inedge_num_def of_nat_1_eq_iff sum_cols_count_eqs)

text\<open>Therefore the column size is always equal to 2 for each column\<close>
lemma mat_K_col_size: "j< n \<Longrightarrow> of_nat (mat_col_size K j) = 2"
proof-
  assume j: "j<n"
  then show "of_nat (mat_col_size K j) = 2"
  proof-
   have el: "elements_mat K \<subseteq> {0, 1, -1}" using K_elems by auto
   then have  "of_nat (mat_col_size K j) = sum_abs_vec (col K j)"
  unfolding mat_col_size_def using j mat_col_size_sum_alt[of K j]
  by (metis dim_col_K mat_col_size_def)  
  thus ?thesis using j sum_incicol_elem_2 
    by (metis of_nat_eq_iff of_nat_numeral)
qed
qed

end
end