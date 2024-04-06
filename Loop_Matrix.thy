theory Loop_Matrix
 imports Network_Loop_System
          Incidence_Matrix

begin

subsection \<open>Loop Vector\<close> 

context nonempty_loop_system
begin

definition loop_vec_of :: "'a edges list \<Rightarrow> 'a edge \<Rightarrow> ('b:: {field_char_0}) vec" where
"loop_vec_of Ls p \<equiv> vec (length Ls) (\<lambda>k. if p \<in> set (loop_list (Ls!k)) then 1
                                       else if p \<in> set (reverse (loop_list (Ls!k))) then -1 else 0)"

lemma loop_cvec_elems: "set\<^sub>v (loop_vec_of Ls p) \<subseteq> {0, 1, -1}"
  by (auto simp add: vec_set_def loop_vec_of_def)

lemma finite_loop_cvec_elems: "finite (set\<^sub>v (loop_vec_of Ls p))"
using finite_subset loop_cvec_elems by blast

lemma loop_cvec_dim: "dim_vec (loop_vec_of Ls p) = length Ls" 
  by (simp add: loop_vec_of_def)

lemma loop_cvec_index: "k < length Ls \<Longrightarrow> loop_vec_of Ls p $ k = (if p \<in> set (loop_list (Ls!k)) then 1
        else if p \<in> set (reverse (loop_list (Ls!k))) then -1 else 0)"
  by(simp add: loop_vec_of_def)

lemma loop_vec_pos: "k < length Ls \<Longrightarrow> (p \<in> set (loop_list (Ls!k)) \<and> p \<notin> set (reverse (loop_list (Ls!k)))) \<or> (p \<in> set (loop_list (Ls!k)) \<and> p \<in> set (reverse (loop_list (Ls!k))))
    \<Longrightarrow> (loop_vec_of Ls p) $k = 1"
    unfolding loop_vec_of_def by auto

lemma loop_vec_neg:  "k < length Ls \<Longrightarrow> p \<in> set (reverse (loop_list (Ls!k)))  \<Longrightarrow> p \<notin> set (loop_list (Ls!k))
    \<Longrightarrow> (loop_vec_of Ls p) $ k = -1"
  unfolding loop_vec_of_def by auto    

lemma loop_vec_0: "k < length Ls  \<Longrightarrow> p \<notin> set (loop_list (Ls!k)) \<Longrightarrow> p \<notin> set (reverse (loop_list (Ls!k)))
    \<Longrightarrow> (loop_vec_of Ls p) $ k = 0"
  by(simp add: loop_vec_of_def)

lemma loop_cvec_index_mone: "k < length Ls \<Longrightarrow> loop_vec_of Ls p $ k = -1 \<longleftrightarrow> p \<in> set (reverse (loop_list (Ls!k))) \<and> p \<notin> set (loop_list (Ls!k))"
 by(simp add: loop_vec_of_def)

lemma loop_cvec_index_one: "k < length Ls  \<Longrightarrow>  loop_vec_of Ls p $ k = 1 \<longleftrightarrow> p \<in> set (loop_list (Ls!k))"
  by(simp add: loop_vec_of_def)
  
lemma loop_cvec_index_zero: "k < length Ls \<Longrightarrow> loop_vec_of Ls p $ k = 0 \<longleftrightarrow> p \<notin> set (loop_list (Ls!k)) \<and> p \<notin> set (reverse (loop_list (Ls!k)))"
  by(simp add: loop_vec_of_def)

subsection \<open>Loop Row Vector\<close>

definition loop_rvec_of :: "'a edges  \<Rightarrow> 'a edges  \<Rightarrow> ('b :: {field_char_0}) vec" where
"loop_rvec_of L Es \<equiv> vec (length Es) (\<lambda>j. if (Es!j) \<in> set (loop_list L) then 1
 else if (Es!j) \<in> set (reverse (loop_list L)) then -1 else 0)"

lemma loop_rvec_elems: "set\<^sub>v (loop_rvec_of L Es) \<subseteq> {0, 1, -1}"
  by (auto simp add: vec_set_def loop_rvec_of_def)

lemma finite_loop_rvec_elems: "finite (set\<^sub>v (loop_rvec_of L Es))"
  using finite_subset loop_rvec_elems by blast

lemma loop_rvec_dim: "dim_vec (loop_rvec_of L Es) = length Es" by (simp add: loop_rvec_of_def)

lemma loop_rvec_index: "j < length Es \<Longrightarrow> loop_rvec_of L Es $ j= (if (Es!j) \<in> set (loop_list L) then 1
 else if (Es!j) \<in> set (reverse (loop_list L)) then -1 else 0)"
  by(simp add: loop_rvec_of_def)

lemma loop_rvec_index_mone: "j < length Es  \<Longrightarrow>loop_rvec_of L Es $ j = -1  \<longleftrightarrow> (Es!j) \<in> set (reverse (loop_list L)) \<and>  Es ! j \<notin> set (loop_list L)"
  by(simp add: loop_rvec_of_def)

lemma loop_rvec_index_one: "j < length Es \<Longrightarrow>  loop_rvec_of L Es $ j = 1 \<longleftrightarrow> (Es!j) \<in> set (loop_list L)"
   by(simp add: loop_rvec_of_def)

lemma loop_rvec_index_zero: "j < length Es \<Longrightarrow> loop_rvec_of L Es $ j = 0 \<longleftrightarrow> (Es!j) \<notin> set (reverse (loop_list L)) \<and> (Es!j) \<notin> set (loop_list L)"
  by(simp add: loop_rvec_of_def)

subsection \<open>Loop Matrix whose elements are  0, 1,and  -1\<close>

definition loop_matrix :: "'a edges list \<Rightarrow> 'a edges  \<Rightarrow> ('b :: {field_char_0}) mat" where
"loop_matrix Ls Es  \<equiv>  mat (length Ls) (length Es) 
(\<lambda>(k,j). if (Es!j) \<in> set (loop_list (Ls!k)) then 1  else if (Es!j) \<in> set (reverse (loop_list (Ls!k))) then -1 
else 0)"

lemma loop_matcol_dim: "dim_col (loop_matrix Ls Es) = length Es" 
  by (simp add: loop_matrix_def)

lemma loop_matrow_dim: "dim_row (loop_matrix Ls Es) = length Ls" 
  by (simp add: loop_matrix_def)

lemma loop_mat_elems: "elements_mat (loop_matrix Ls Es) \<subseteq> {0, 1, -1}"
  by (auto simp add: elements_mat_def loop_matrix_def)

lemma finite_loop_mat_elems: "finite (elements_mat (loop_matrix Ls Es))"
  using finite_subset loop_mat_elems by blast

lemma loop_index[simp]: "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> 
loop_matrix Ls Es  = mat (length Ls) (length Es) (\<lambda>(k,j). if (Es!j) \<in> set (loop_list (Ls!k)) then 1 else if (Es!j) \<in> set (reverse (loop_list (Ls!k)))  then -1  else 0)"
  unfolding loop_matrix_def by blast

lemma loop_carrier[simp]: "loop_matrix Ls Es \<in> carrier_mat (length Ls) (length Es)" 
  unfolding carrier_mat_def by (auto simp add: loop_matcol_dim loop_matrow_dim)

lemma loop_matrix_pos: "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> ((Es!j) \<in> set (loop_list (Ls!k)) \<and> (Es!j) \<notin> set (reverse (loop_list (Ls!k)))) \<or> ((Es!j) \<in> set (loop_list (Ls!k)) \<and> (Es!j) \<in> set (reverse (loop_list (Ls!k))))
    \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 1"
    unfolding loop_matrix_def by auto

lemma loop_matrix_neg:  "k < length Ls \<Longrightarrow> j < length Es  \<Longrightarrow> (Es!j) \<in> set (reverse (loop_list (Ls!k)))  \<Longrightarrow> (Es!j) \<notin> set (loop_list (Ls!k))
    \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = -1"
  unfolding loop_matrix_def by auto    

lemma loop_matrix_0: "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> (Es!j) \<notin> set (loop_list (Ls!k)) \<Longrightarrow> (Es!j) \<notin> set (reverse (loop_list (Ls!k)))
    \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 0"
  by(simp add: loop_matrix_def)

lemma loop_matrix_one_pos: "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 1
    \<Longrightarrow> (Es!j) \<in> set (loop_list (Ls!k))"
  by (metis loop_matrix_0 loop_matrix_neg one_neq_neg_one zero_neq_one)

lemma loop_matrix_mone_neg: "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = -1
    \<Longrightarrow> (Es!j) \<in> set (reverse (loop_list (Ls!k)))"
  by (metis loop_matrix_0 loop_matrix_pos one_neq_neg_one zero_neq_neg_one)

lemma loop_matrix_zero_no: "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 0
    \<Longrightarrow> (Es!j) \<notin> set (loop_list (Ls!k)) \<Longrightarrow>  (Es!j) \<notin> set (reverse (loop_list (Ls!k)))"
  by (metis loop_matrix_neg zero_neq_neg_one)

lemma loop_matrix_one_pos_iff:  "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 1  \<longleftrightarrow> (Es!j) \<in> set (loop_list (Ls!k))"
  using loop_matrix_pos loop_matrix_one_pos by auto

lemma loop_matrix_mone_neg_iff:  "k < length Ls \<Longrightarrow> j < length Es  \<Longrightarrow> (Es!j) \<notin> set (loop_list (Ls!k))
 \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = -1  \<longleftrightarrow> (Es!j) \<in> set (reverse (loop_list (Ls!k)))"
  using loop_matrix_neg loop_matrix_mone_neg by auto

lemma loop_matrix_zero_no_iff:  "k < length Ls \<Longrightarrow> j < length Es 
\<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 0  \<longleftrightarrow> (Es!j) \<notin> set (loop_list (Ls!k)) \<and> (Es!j) \<notin> set (reverse (loop_list (Ls!k)))"
   using loop_matrix_0 by auto

lemma loop_matrix_mone_implies: "H \<subseteq> {..<length Ls} \<Longrightarrow> j < length Es \<Longrightarrow> 
    (\<And> k. k\<in>H \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = -1) \<Longrightarrow> k \<in> H \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j) \<Longrightarrow> (Es!j) \<notin> set (loop_list (Ls!k)) \<Longrightarrow> (Es!j) \<in> set (reverse (loop_list (Ls!k)))"
  using loop_matrix_mone_neg_iff by blast

lemma loop_matrix_one_implies: "H \<subseteq> {..<length Ls} \<Longrightarrow> j < length Es \<Longrightarrow> 
    (\<And> k. k\<in>H \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 1) \<Longrightarrow> k \<in> H \<Longrightarrow> fst (Es!j) \<noteq> snd (Es!j)  \<Longrightarrow> (Es!j) \<in> set(loop_list (Ls!k))"
  using loop_matrix_one_pos_iff by blast

lemma loop_matrix_zero_implies: "H \<subseteq> {..<length Ls} \<Longrightarrow> j < length Es \<Longrightarrow> 
    (\<And> k. k\<in>H \<Longrightarrow> (loop_matrix Ls Es) $$ (k, j) = 0) \<Longrightarrow> k \<in> H \<Longrightarrow> (Es!j) \<notin> set (loop_list (Ls!k)) \<Longrightarrow> (Es!j) \<notin> set (reverse (loop_list (Ls!k)))"
  using loop_matrix_zero_no_iff by blast

text \<open>Reasoning on Columns/Rows of the loop matrix\<close>

lemma loop_matrix_col_def:  "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> 
(col (loop_matrix Ls Es) j) $ k = (if (Es!j) \<in> set (loop_list (Ls!k)) then 1 else if (Es!j) \<in> set (reverse (loop_list (Ls!k))) then -1 else 0)"
  by (simp add: loop_matrix_def)

lemma loop_matrix_col_list_map_elem:  "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> 
(col (loop_matrix Ls Es) j) $ k =  map_vec 
    (\<lambda> X . if (Es!j) \<in> set (loop_list X) then 1 else if (Es!j) \<in> set (reverse (loop_list X))  then -1 else 0) (vec_of_list Ls) $ k"
  by (simp add: loop_matrix_col_def vec_of_list_index)

lemma loop_mat_col_list_map:  "j < length Es \<Longrightarrow> 
    col (loop_matrix Ls Es) j = map_vec (\<lambda> X. if (Es!j) \<in> set (loop_list X) then 1 else if (Es!j) \<in> set (reverse (loop_list X)) then -1 else 0) (vec_of_list Ls)"
by (intro eq_vecI,
    simp_all add: loop_matcol_dim loop_matrow_dim loop_matrix_col_list_map_elem index_vec_of_list loop_matrix_def)

lemma loop_matrix_row_def:  "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> 
(row (loop_matrix Ls Es) k) $ j = (if (Es!j) \<in> set (loop_list (Ls!k)) then 1 else if (Es!j) \<in> set (reverse (loop_list (Ls!k))) then -1 else 0)"
  by (simp add: loop_matrix_def)

lemma loop_matrix_row_list_map_elem:  "k < length Ls \<Longrightarrow> j < length Es \<Longrightarrow> 
(row (loop_matrix Ls Es) k) $ j = map_vec 
    (\<lambda> y. if y \<in>  set (loop_list (Ls!k)) then 1  else if y \<in> set (reverse (loop_list (Ls!k)))
 then -1 else 0) (vec_of_list Es) $ j"
  by (simp add: loop_matrix_row_def vec_of_list_index)

lemma loop_matrix_row_map:  "k < length Ls \<Longrightarrow>
   row (loop_matrix Ls Es) k = map_vec (\<lambda> y. if  y \<in> set (loop_list (Ls!k)) then 1  else if y \<in> set (reverse (loop_list (Ls!k))) then -1 else 0) (vec_of_list Es)"
proof(intro eq_vecI)
  show "\<And>i. k < length Ls \<Longrightarrow>
         i < dim_vec (map_vec (\<lambda>y. if y \<in> set (loop_list (Ls ! k)) then 1 else if y \<in> set (reverse (loop_list (Ls ! k))) then - 1 else 0) (vec_of_list Es)) \<Longrightarrow>
         row (loop_matrix Ls Es) k $ i = map_vec (\<lambda>y. if y \<in> set (loop_list (Ls ! k)) then 1 else if y \<in> set (reverse (loop_list (Ls ! k))) then - 1 else 0) (vec_of_list Es) $ i"
    using loop_matrix_row_def by (simp add: vec_of_list_alt)
  show " k < length Ls \<Longrightarrow> dim_vec (row (loop_matrix Ls Es) k) = dim_vec (map_vec (\<lambda>y. if y \<in> set (loop_list (Ls ! k)) then 1 else if y \<in> set (reverse (loop_list (Ls ! k))) then - 1 else 0) (vec_of_list Es))"
    by (simp add: loop_matcol_dim)
qed

text \<open>Connection between the loop vectors and the loop matrix\<close>

lemma loop_colmat_loop_vec: " j < length Es \<Longrightarrow>  col (loop_matrix Ls Es) j = loop_vec_of Ls (Es ! j)"
  by (auto simp add: loop_matrix_def loop_vec_of_def)

lemma loop_colsmat_loop_vecs: 
  assumes "\<forall>j \<in> {0..< length Es}. fst (Es!j) \<noteq> snd (Es!j)"
  shows "cols (loop_matrix Ls Es) = map (\<lambda> j. loop_vec_of Ls j) Es"
proof (intro nth_equalityI)
  have l1: "length (cols (loop_matrix Ls Es)) = length Es"
    using loop_matcol_dim by simp
  have l2: "length (map (\<lambda> j. loop_vec_of Ls j) Es) = length Es"
    using length_map by simp
  then show "length (cols (loop_matrix Ls Es)) = length (map (loop_vec_of Ls) Es)" 
    using l1 l2 by simp
  show "\<And>i. i < length (cols (loop_matrix Ls Es)) \<Longrightarrow> cols (loop_matrix Ls Es) ! i = map (loop_vec_of Ls) Es ! i "
    by (simp add:loop_matcol_dim loop_colmat_loop_vec)
qed

lemma loop_rowmat_loop_rvec: " k < length Ls \<Longrightarrow> row (loop_matrix Ls Es) k = loop_rvec_of (Ls!k) Es"
  using  loop_matrix_row_def loop_rvec_of_def 
  by (smt (verit, best) loop_matcol_dim loop_matrix_0 loop_matrix_neg loop_matrix_one_pos_iff row_def vec_cong)

lemma loop_rowsmat_loop_rvecs: 
  shows "rows (loop_matrix Ls Es) = map (\<lambda> k. loop_rvec_of k Es) Ls"
  using loop_rowmat_loop_rvec 
  by (metis (no_types, lifting) length_rows loop_matrow_dim map_nth_eq_conv nth_rows)

text\<open>For all rows of the loop matrix whose elements are only 1, -1 or 0, there are non zero elements which are 1 or -1\<close>

definition nempty_row :: "('b :: {field_char_0}) mat \<Rightarrow> nat \<Rightarrow> bool" where
"nempty_row A i \<equiv> \<exists> x. x \<noteq> 0 \<and> x \<in>$ row A i"

lemma nempty_row_obtains: 
  assumes "nempty_row A i"
  obtains j1 j2 where "j1 < dim_col A" and "j2 < dim_col A" and "(row A i) $ j1 \<noteq> 0" and "(row A i) $ j2 \<noteq> 0"
proof -
  have d: "dim_vec (row A i) = dim_col A" by simp
  from assms obtain k1 k2 where "k1 \<noteq> 0" and "k2 \<noteq> 0" and "k1 \<in>$ row A i" and "k2 \<in>$ row A i"
    by (auto simp add: nempty_row_def)
  thus ?thesis using vec_contains_obtains_index d
    by (metis that) 
qed

lemma nempty_row_alt: 
  assumes "i < dim_row A" 
  shows "nempty_row A i \<longleftrightarrow> (\<exists> j1 j2. j1 < dim_col A \<and> j2 < dim_col A \<and> A $$ (i, j1) \<noteq> 0  \<and> A $$ (i, j2) \<noteq> 0)"
proof
  show "nempty_row A i \<Longrightarrow> \<exists>j1 j2. j1 < dim_col A \<and> j2 < dim_col A \<and> A $$ (i, j1) \<noteq> 0 \<and> A $$ (i, j2) \<noteq> 0"
    using assms nempty_row_obtains by (metis index_row(1))
next
  assume "\<exists>j1 j2. j1 < dim_col A \<and> j2 < dim_col A \<and> A $$ (i, j1) \<noteq> 0 \<and> A $$ (i, j2) \<noteq> 0"
   then obtain j1 j2 where jlt: "j1 <dim_col A" and "j2 <dim_col A" and ne: "A $$ (i, j1) \<noteq> 0" "A $$ (i, j2) \<noteq> 0" by blast
    then have jlt1: "j1 < dim_vec (row A i)" "j2 < dim_vec (row A i)" by auto
    then have "(row A i) $ j1 \<noteq> 0" "(row A i) $ j2 \<noteq> 0" using ne assms by auto
    then obtain k1 k2 where "(row A i) $ j1 = k1"  "(row A i) $ j2 = k2" and "k1 \<noteq> 0" "k2 \<noteq> 0"
    by simp
    then show "nempty_row A i" using nempty_row_def jlt jlt1 
      by (metis vec_setI)
  qed

text \<open>Define a real-valued loop matrix represents the nonempty loop system \<close>

abbreviation C :: "real mat" where
"C \<equiv> loop_matrix \<L>s \<E>s"

lemma C_alt_def: "C = mat l n (\<lambda> (k,j). if in_pos_loop (\<E>s!j) (\<L>s!k) then 1 else if in_neg_loop (\<E>s!j) (\<L>s!k) then -1 else 0)"
  by (smt (verit, best) cong_mat edge_loop1 in_pos_loop loop_matrix_def not_inpos_inneg_loop' nth_mem prod.simps(2))

lemma inpos_loop_C_one_iff: "k < dim_row C \<Longrightarrow> j < dim_col C \<Longrightarrow> in_pos_loop (\<E>s!j) (\<L>s!k) \<longleftrightarrow> C $$ (k,j) = 1"
  by (simp add: C_alt_def)
 
lemma inneg_loop_C_mone_iff: "k < dim_row C \<Longrightarrow> j < dim_col C \<Longrightarrow> in_neg_loop (\<E>s!j) (\<L>s!k) \<longleftrightarrow> C $$ (k,j) = -1"
  using C_alt_def in_neg_loop 
  by (smt (verit, best) inpos_loop_C_one_iff loop_matcol_dim loop_matrix_mone_neg_iff loop_matrow_dim loop_rev_set loop_set not_in_loop_indexed valid_edges_index valid_loops_index)

lemma not_inloop_C_zero: "k < dim_row C \<Longrightarrow> j < dim_col C \<Longrightarrow> \<not> in_neg_loop (\<E>s!j) (\<L>s!k)
                             \<Longrightarrow> \<not> in_pos_loop (\<E>s!j) (\<L>s!k) \<Longrightarrow> C $$ (k,j) = 0"
  by (simp add: C_alt_def)

lemma not_inloop_C_zero_iff: assumes "k < dim_row C" "j < dim_col C "
  shows "\<not> in_neg_loop (\<E>s!j) (\<L>s!k)
                             \<and>  \<not> in_pos_loop (\<E>s!j) (\<L>s!k) \<longleftrightarrow> C $$ (k,j) = 0"
  using assms inneg_loop_C_mone_iff inpos_loop_C_one_iff
  by (metis not_inloop_C_zero one_neq_zero zero_neq_neg_one)

lemma lloop_list: "k < dim_row C \<Longrightarrow> (\<L>s!k) = loop_list (\<L>s!k)" 
  using loop_list_def wellformed_2  by (simp add: loop_matrow_dim)

lemma C_index_val_alt: " k < dim_row C \<Longrightarrow> j < dim_col C \<Longrightarrow> 
    C $$ (k, j) = (if (\<E>s!j) \<in> set (loop_list (\<L>s!k)) then 1  else if (\<E>s!j) \<in> set (reverse (loop_list (\<L>s!k))) then -1 else 0)"
  using inpos_loop_C_one_iff lloop_list by (simp add: loop_matrix_def)

text \<open>Matrix Dimension related lemmas \<close>
 
lemma C_carrier_mat: "C \<in> carrier_mat l n" 
  by (simp add: loop_matrix_def)

lemma dim_row_is_l[simp]: "dim_row C = l"
  using C_carrier_mat by blast

lemma dim_col_C[simp]: "dim_col C = n"
   using loop_matcol_dim by blast 

lemma dim_vec_row_C: "dim_vec (row C k) = n"
  by simp

lemma dim_vec_col_C: "dim_vec (col C k) = l"
  by simp 

lemma dim_vec_C_col: 
  assumes "j < n"
  shows "dim_vec (cols C ! j) = l"
  using assms by simp

lemma C_elems: "elements_mat (C) \<subseteq> {0, 1, -1}"
  by (auto simp add: loop_matrix_def elements_mat_def)

text \<open>Transpose properties \<close>

lemma transpose_C_mult_dim: "dim_row (C * C\<^sup>T) = l" "dim_col (C * C\<^sup>T) = l"
  by (simp_all)

lemma C_trans_index_val: "k < dim_col C \<Longrightarrow> j < dim_row C \<Longrightarrow> 
    C\<^sup>T $$ (k, j) = (if (in_pos_loop (\<E>s!k) (\<L>s!j)) then 1 else if (in_neg_loop (\<E>s!k) (\<L>s!j)) then -1 else 0)"
  using C_alt_def by force

lemma C_trans_index_val_alt: " k < dim_col C \<Longrightarrow> j < dim_row C \<Longrightarrow> 
    C\<^sup>T $$ (k, j) = (if (\<E>s!k) \<in> set (loop_list (\<L>s!j)) then 1  else if (\<E>s!k) \<in> set (reverse (loop_list (\<L>s!j))) then -1 else 0)"
  using C_trans_index_val inpos_loop_C_one_iff lloop_list by fastforce
                           
lemma transpose_entries: "elements_mat (C\<^sup>T) \<subseteq> {0, 1, -1}"
  using C_trans_index_val elements_matD 
  by (metis index_transpose_mat(2) index_transpose_mat(3) insertCI subsetI)

text \<open>Loop Matrix elements and index related lemmas \<close>

lemma C_mat_row_elems: "k < l \<Longrightarrow> vec_set (row C k) \<subseteq> {0, 1, -1}"
  by (metis C_elems dim_row_is_l row_elems_subset_mat subset_trans)

lemma C_mat_col_elems: "j < n \<Longrightarrow> vec_set (col C j) \<subseteq> {0, 1, -1}"
  by (metis C_elems col_elems_subset_mat dim_col_C subset_trans)

lemma C_matrix_elems_one_mone_zero: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = 0 \<or> C $$ (k, j) = 1 \<or> C $$ (k, j) = -1" 
  by (simp add: loop_matrix_def)

lemma C_not_zero_simp: "j < dim_col C \<Longrightarrow> k < dim_row C \<Longrightarrow> C $$ (k, j) \<noteq> 0 \<Longrightarrow> C $$ (k, j) = 1 \<or> C $$ (k, j) = -1"
  using loop_mat_elems[of "\<L>s" "\<E>s"] by blast

lemma C_not_one_simp: "j < dim_col C \<Longrightarrow> k < dim_row C \<Longrightarrow> C $$ (k, j) \<noteq> 1 \<Longrightarrow> C $$ (k, j) = 0 \<or> C $$ (k, j) = -1"
  using loop_mat_elems[of "\<L>s" "\<E>s"] by blast

lemma C_not_mone_simp: "j < dim_col C \<Longrightarrow> k < dim_row C \<Longrightarrow> C $$ (k, j) \<noteq> -1 \<Longrightarrow> C $$ (k, j) = 0 \<or> C $$ (k, j) = 1"
  using loop_mat_elems[of "\<L>s" "\<E>s"] by blast

lemma C_not_Mone_simp: "j < dim_col C \<Longrightarrow> k < dim_row C \<Longrightarrow> C $$ (k, j) \<noteq> 1 \<Longrightarrow> C $$ (k, j) \<noteq> -1 \<Longrightarrow> C $$ (k, j) = 0"
  using C_not_mone_simp  by blast

lemma C_ge0[simp]: "j < dim_col C \<Longrightarrow> i < dim_row C \<Longrightarrow> C $$ (i, j) > 0 \<Longrightarrow>  C $$ (i, j) = 1"
  using C_elems C_matrix_elems_one_mone_zero 
  by (smt (verit) dim_col_C dim_row_is_l)

lemma C_le0[simp]: "j < dim_col C \<Longrightarrow> i < dim_row C \<Longrightarrow> C $$ (i, j) < 0 \<Longrightarrow>  C $$ (i, j) = -1"
  using C_elems C_matrix_elems_one_mone_zero 
  by (smt (verit) dim_col_C dim_row_is_l)

lemma C_index_square_itself: "j < dim_col C \<Longrightarrow> k < dim_row C \<Longrightarrow> (C $$ (k, j))^2 = abs (C $$ (k, j))"
  using C_not_zero_simp by simp

lemma C_row_index_square_itself: "j < dim_col C \<Longrightarrow> k < dim_row C \<Longrightarrow> ((row C k) $ j)^2 = abs ((row C k) $ j)"
  using index_row  C_index_square_itself by auto 

lemma C_matrix_edge_in_revloop: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = -1 \<Longrightarrow>  (\<E>s ! j) \<in> set (reverse ((\<L>s ! k)))"
  using wellformed_1 lloop_list
  by (metis inneg_loop_C_mone_iff loop_matcol_dim loop_matrow_dim wf_neg_loop)
 
lemma C_matrix_edge_in_loop: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = 1 \<Longrightarrow> (\<E>s ! j) \<in> set (\<L>s ! k)"
  by (metis inpos_loop_C_one_iff loop_matcol_dim loop_matrow_dim wf_pos_loop)

lemma C_matrix_edge_notin_loop_iff: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = 0 \<longleftrightarrow> (\<E>s ! j) \<notin>  set (\<L>s ! k) \<and> (\<E>s ! j) \<notin> set (reverse (\<L>s ! k))"
  using loop_matrix_zero_no_iff  C_matrix_edge_in_loop C_matrix_edge_in_revloop 
  by (metis lloop_list loop_matrow_dim)
 
lemma C_matrix_pos_iff: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = 1 \<longleftrightarrow> (\<E>s ! j) \<in> set (\<L>s ! k) "
  using C_matrix_edge_in_loop 
  by (metis lloop_list loop_matrix_one_pos_iff loop_matrow_dim)

lemma C_matrix_neg_iff: "k < l \<Longrightarrow> j < n \<Longrightarrow> C $$ (k, j) = -1 \<longleftrightarrow> (\<E>s ! j) \<in> set (reverse (\<L>s ! k)) \<and> (\<E>s ! j) \<notin> set (\<L>s ! k) "
  using  C_matrix_pos_iff C_matrix_edge_notin_loop_iff
  by (smt (verit, best) C_matrix_elems_one_mone_zero)

text \<open>Loop Vector is a column of the loop matrix\<close>

lemma col_loop_vec: "j < length \<E>s \<Longrightarrow> loop_vec_of \<L>s (\<E>s ! j) = col C j"
  by (simp add: loop_colmat_loop_vec) 

lemma row_loop_vec: "k < length \<L>s \<Longrightarrow> loop_rvec_of (\<L>s!k) \<E>s = row C k"
  by (simp add: loop_rowmat_loop_rvec)

text \<open>Loop matrix column properties\<close>

lemma C_col_def: "j < n \<Longrightarrow> k < l \<Longrightarrow> (col C j) $ k = ( if (\<E>s ! j) \<in> set ((\<L>s ! k)) then 1
  else if (\<E>s ! j) \<in> set (reverse (\<L>s ! k)) then -1 else 0)"
  using lloop_list by auto

lemma C_col_def_indiv: 
     "j < n \<Longrightarrow> k < l \<Longrightarrow> (\<E>s ! j) \<notin> set (\<L>s ! k) \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! k)) \<longleftrightarrow> (col C j) $ k = -1"
     "j < n \<Longrightarrow> k < l \<Longrightarrow> (\<E>s ! j) \<in> set (\<L>s ! k) \<longleftrightarrow> (col C j) $ k = 1"
     "j < n \<Longrightarrow> k < l \<Longrightarrow> (\<E>s ! j) \<notin> set (reverse (\<L>s ! k)) \<and> (\<E>s ! j) \<notin> set (\<L>s ! k) \<longleftrightarrow> (col C j) $ k = 0"
  using C_col_def 
  apply force+
  done

lemma C_col_list_map_elem: "j < n \<Longrightarrow> k < l \<Longrightarrow> 
    col C j $ k = map_vec (\<lambda> X . if (\<E>s ! j) \<in> set (X) then 1 else  if (\<E>s!j) \<in> set (reverse X) then -1 else 0) (vec_of_list \<L>s) $ k"
  by (smt (verit, best) C_col_def dim_vec_of_list index_map_vec(1) index_vec_of_list)

lemma C_row_def: "j < n \<Longrightarrow> k < l \<Longrightarrow> (row C k) $ j = (if (\<E>s ! j) \<in> set ((\<L>s ! k)) then 1 
  else if (\<E>s ! j) \<in> set (reverse (\<L>s ! k))  then -1 else 0)"
  using C_matrix_neg_iff C_matrix_pos_iff  C_col_def by auto

lemma C_row_def_indiv: 
     "j < n \<Longrightarrow> k < l \<Longrightarrow> (\<E>s ! j) \<notin> set (\<L>s ! k) \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! k)) \<longleftrightarrow> (row C k) $ j = -1"
     "j < n \<Longrightarrow> k < l \<Longrightarrow> (\<E>s ! j) \<in> set (\<L>s ! k)  \<longleftrightarrow> (row C k) $ j = 1"
     "j < n \<Longrightarrow> k < l \<Longrightarrow> (\<E>s ! j) \<notin> set (reverse (\<L>s ! k)) \<and> (\<E>s ! j) \<notin> set (\<L>s ! k) \<longleftrightarrow> (row C k) $ j = 0"
 using C_row_def
  apply force+
  done

lemma nempty_row_obtains1: 
   assumes "nempty_row C i"  
   obtains j1 j2  where "j1 < dim_col C" and  "j2 < dim_col C" and  "(row C i)$ j1 \<noteq> 0"  
      and "(row C i) $ j2 \<noteq> 0"  and "j1 \<noteq> j2 \<longrightarrow> (row C i)$ j1 = (row C i)$ j2 \<or> (row C i)$ j1 \<noteq> (row C i)$ j2" 
proof-
 have d: "dim_vec (row C i) = dim_col C" 
   by (simp add: loop_matcol_dim)
  obtain  x y where "x \<noteq> 0" and "y \<noteq> 0" and "x \<in>$ (row C i)"  and "y \<in>$ (row C i)" and "x \<noteq> y \<or> x = y"
   using assms 
   by (meson nempty_row_def)
  thus ?thesis
    by (metis d that vec_contains_obtains_index)
qed

lemma nempty_row_01m1: 
  assumes "i < dim_row C" 
  shows "nempty_row C i \<longleftrightarrow> 1 \<in>$ row C i \<or> (-1) \<in>$ (row C i)"
proof (intro iffI)
  assume "nempty_row C i"
  then obtain k1 k2 where kk: "k1 \<noteq> 0"  "k2 \<noteq> 0" and ne : "k1 \<in>$ row C i" "k2 \<in>$ row C i"
    using nempty_row_def by blast
  then have "k1 \<in> elements_mat C" "k2 \<in> elements_mat C" 
    using vec_contains_row_elements_mat assms 
    by metis+
  then have "(k1 = 1 \<or>  k1 = -1) \<and> (k2 = 1 \<or> k2 = -1)"
    using C_elems kk by blast
  thus "1 \<in>$ row C i \<or> (-1) \<in>$ (row C i)"
    using ne by auto
next
  assume "1 \<in>$ row C i \<or> (-1) \<in>$ (row C i)"
  then show "nempty_row C i"
    using nempty_row_def 
    by (metis zero_neq_neg_one zero_neq_one)
qed

lemma nempty_entries_C_row:  
  assumes "i < dim_row C" 
  shows "nempty_row C i \<longleftrightarrow> \<L>s ! i \<noteq> []"  
proof (intro iffI)
  assume "nempty_row C i" 
  then obtain j1 j2 where js: "j1 < dim_col C" "j2 < dim_col C" and "row C i $ j1 \<noteq> 0" "row C i $ j2 \<noteq> 0" 
    using nempty_row_obtains assms by blast
  then have a1: "row C i $ j1 = 1 \<or> row C i $ j1 = -1" "row C i $ j2 = 1 \<or> row C i $ j2 = -1"
    using assms by (metis C_row_def dim_col_C dim_row_is_l)+
  then have "(\<E>s ! j1) \<in> set (\<L>s ! i) \<or> ((\<E>s ! j1) \<notin> set (\<L>s ! i) \<and> (\<E>s ! j1) \<in> set (reverse (\<L>s ! i)))"
            "(\<E>s ! j2) \<in> set (\<L>s ! i) \<or> ((\<E>s ! j2) \<notin> set (\<L>s ! i) \<and> (\<E>s ! j2) \<in> set (reverse (\<L>s ! i)))"
    using assms C_row_def_indiv(1) C_row_def_indiv(2) 
    apply (metis dim_col_C dim_row_is_l js(1)) 
    by (metis C_row_def_indiv(1) C_row_def_indiv(2) a1(2) assms dim_col_C dim_row_is_l js(2))
  then show " \<L>s ! i \<noteq> []"  
    by force
next
  assume b1: "\<L>s ! i \<noteq> []"
  have "\<L>s ! i \<in>  \<L>" using assms by auto
  then obtain j where jj: "j < dim_col C" and cc: "(\<E>s ! j) \<in> set (loop_list (\<L>s ! i)) \<or> ((\<E>s ! j) \<notin> set (\<L>s ! i) \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! i))) "
    using valid_edges_posneg edge_in_loop_pos_inci_node wellformed_1
    by (metis assms dim_col_C dim_row_is_l edge_loop1 edge_reverse edge_symcl_reverse reverse_reverse_list sedge_in_valid_loop valid_edges_index_obtains)
  then have "row C i $ j = 1  \<or> row C i $ j = -1" using jj cc b1 assms
    by (metis C_row_def_indiv(1) C_row_def_indiv(2) dim_col_C dim_row_is_l lloop_list)
  then show "nempty_row C i" using nempty_row_01m1 assms 
    by (metis index_row(2) jj vec_setI)
qed

text \<open>Dimensional connection between the incidence and the loop matrices\<close>

lemma C_dimcol_is_K_dimcol: "dim_col K = dim_col C"
  using dim_col_K dim_col_C by presburger

lemma dimcol_is_K_tC: "dim_col K = dim_row C\<^sup>T"
  by simp

lemma dimrow_K_tC: "dim_row (K * C\<^sup>T) = m"
   using dim_row_K 
   by (metis index_mult_mat(2))

lemma dimcol_tCK: "dim_col (K * C\<^sup>T) = l"
  by simp

text \<open>Degree of a loop matrix with respect to each row is equal to the number of nonzero elements of each row\<close>

lemma ones_inrow: 
 assumes "i < dim_row C"
 shows "(mat_out_degree_num C i) = card {j. j<n \<and> (\<E>s ! j) \<in> set (\<L>s ! i)}"
  using C_matrix_pos_iff mat_out_deg_num_alt[of i C] 
  by (smt (verit, best) Collect_cong assms dim_col_C dim_row_is_l lloop_list)

lemma mones_inrow: 
 assumes "i < dim_row C"
 shows "mat_in_degree_num C i = card {j. j<n  \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! i)) \<and> (\<E>s ! j) \<notin> set (\<L>s ! i)}"
  using ones_inrow C_matrix_neg_iff assms dim_row_is_l mat_in_deg_num_alt[of i C] 
  by (smt (verit, best) Collect_cong loop_matcol_dim)

lemma degree_of_loop: 
 assumes "i < dim_row C"
 shows "mat_degree_num C i = card {j. j<n  \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! i)) \<and> (\<E>s ! j) \<notin> set (\<L>s ! i)} + card {j. j<n \<and> (\<E>s ! j) \<in> set (\<L>s ! i)}"
  using assms mones_inrow ones_inrow by (simp add: mat_degree_num_def)

lemma degree_of_loop_sumabs: 
 assumes "i < dim_row C"
 shows "mat_degree_num C i = sum_abs_vec (row C i)"
  using C_elems assms mat_degree_property by blast

text \<open>A loop consists of elements that they correspond to nonzero entries in a row of the loop matrix\<close>

definition aloop_size where 
  "aloop_size ls = card {j. j < n \<and> (\<E>s ! j) \<in> set ls} + card {j. j < n \<and> (\<E>s ! j) \<in> set (reverse ls) \<and> (\<E>s ! j) \<notin> set ls}"

lemma aloopsize_sumabs: 
  assumes "i < dim_row C" 
  shows "(aloop_size (\<L>s ! i)) = sum_abs_vec (row C i)"
proof-
  {have "card {j. (\<E>s ! j) \<in> set (\<L>s ! i) \<and> j < n} = mat_out_degree_num C i" 
    using assms ones_inrow 
    by (metis (no_types, lifting) Collect_cong)} note o1 = this
  {have "card {j. (\<E>s ! j) \<notin> set (\<L>s ! i) \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! i)) \<and> j < n} = mat_in_degree_num C i" 
    using assms mones_inrow by (metis (no_types, lifting) Collect_cong)} note i1 = this
  have "of_nat (aloop_size (\<L>s ! i)) = card {j. j < n \<and>  (\<E>s ! j) \<in> set (\<L>s ! i)} + card {j. j < n \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! i)) \<and> (\<E>s ! j) \<notin> set (\<L>s ! i)}"
    by(simp add: aloop_size_def)    
  thus ?thesis using assms o1 i1 degree_of_loop degree_of_loop_sumabs 
    by (smt (verit, ccfv_threshold) Collect_cong add.commute of_nat_id)
qed

lemma aloop_size_degree: "i < dim_row C \<Longrightarrow> aloop_size (\<L>s ! i) = mat_degree_num C i"
  by (metis C_elems aloopsize_sumabs mat_degree_property of_nat_eq_iff)

lemma aloopsize_scalar:
  assumes "i < dim_row C" 
  shows "of_nat (aloop_size (\<L>s ! i)) = (row C i) \<bullet> (row C i)"
  using assms aloopsize_sumabs 
  by (simp add: C_elems mat_degree_property scalar_prod_inc_vec_degree_num_mat)

lemma aloopsize_transposemult:
  assumes "i < dim_row C" 
  shows "of_nat (aloop_size (\<L>s ! i)) = (C * (transpose_mat C)) $$ (i,i)"
  using assms mat_degree_alt aloopsize_sumabs
  by (metis C_elems degree_of_loop_sumabs)

lemma aloopsize_trace:
  shows "(\<Sum> i \<in> {..< l}. of_nat (aloop_size (\<L>s ! i))) = trace (C * (transpose_mat C))"
proof- 
  have "(\<Sum> i \<in> {..< l}. of_nat (aloop_size (\<L>s ! i))) = (\<Sum> i \<in> {..< l}. (row C i) \<bullet> (row C i) ) "   
    using aloopsize_scalar  by simp
  also have "... = trace (C * (transpose_mat C))"
     unfolding trace_def by (simp add: atLeast0LessThan)
   finally show ?thesis by auto
qed

text \<open>Relationship between node-edge-loop\<close>

lemma pos_loop_neg_inci_if:
  assumes  "x \<in> \<E>" and "es \<in> set \<L>s"
  shows "snd x = y \<and> x \<in> set (loop_list es) \<Longrightarrow> fst x \<noteq> y \<and> (x \<notin> set (reverse es) \<or> x \<in> set (reverse es))"
  using assms 
  by (meson exists_nodes)

lemma pos_loop_pos_inci_if:
  assumes  "x \<in> \<E>" and "es \<in> set \<L>s"
  shows "fst x = y \<and> x \<in> set (loop_list es) \<Longrightarrow> snd x \<noteq> y \<and> (x \<notin> set (reverse es) \<or> x \<in> set (reverse es))"
  using assms no_self_loop by blast

lemma neg_loop_pos_inci_if:
  assumes  "x \<in> \<E>" and "es \<in> set \<L>s"
  shows "fst x = y \<and> x \<in> set(reverse es) \<Longrightarrow> snd x \<noteq> y \<and> (x \<notin> set (loop_list es) \<or> x \<in> set es)"
  using assms exists_nodes loop_set by blast

lemma neg_loop_neg_inci_if:
  assumes  "x \<in> \<E>" and "es \<in> set \<L>s"
  shows "snd x = y \<and> x \<in> set(reverse es) \<Longrightarrow> fst x \<noteq> y \<and> (x \<notin> set (loop_list es) \<or> x \<in> set es)"
 using assms exists_nodes 
  by (metis loop_set)

end
end