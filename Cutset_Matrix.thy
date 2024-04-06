theory Cutset_Matrix
 imports  Network_Cutset_System
          Loop_Matrix
          
begin


subsection \<open>Cutset Vectors\<close>

context nonempty_cutset_system
begin

text \<open> Cutset column vector \<close>  

definition cutset_vec :: "'a edges list \<Rightarrow> 'a \<times> 'a \<Rightarrow> ('b :: {field_char_0}) vec" where
"cutset_vec Cs p  \<equiv> vec (length Cs) (\<lambda>i. if  \<not> (in_pos_cutset (N!i) p (Cs ! i)) \<and> in_neg_cutset (N!i) p (Cs ! i) then -1
        else if in_pos_cutset (N!i) p (Cs ! i) \<and> \<not> (in_neg_cutset (N!i) p (Cs ! i))  then 1 else 0)"

lemma cutset_vec_elems: "set\<^sub>v (cutset_vec Cs p) \<subseteq> {0, 1, -1}"
  by (auto simp add: vec_set_def cutset_vec_def)

lemma finite_cutset_vec: "finite (set\<^sub>v (cutset_vec Cs p))"
  by (auto simp add: vec_set_def cutset_vec_def)

lemma cutset_vec_dim: "dim_vec (cutset_vec Cs p) = length Cs" by (simp add: cutset_vec_def)

lemma cutset_vec_index: "i < length Cs \<Longrightarrow>
 cutset_vec Cs p $ i = (if \<not> (in_pos_cutset (N!i) p (Cs ! i)) \<and> in_neg_cutset (N!i) p (Cs ! i) then -1
        else if in_pos_cutset (N!i) p (Cs ! i) \<and> \<not> (in_neg_cutset (N!i) p (Cs ! i))  then 1  else 0)"
  by (simp add: cutset_vec_def)

lemma cutset_vec_index_mone_negc: "i < length Cs \<Longrightarrow> cutset_vec Cs p $ i = -1 \<longleftrightarrow> in_neg_cutset (N!i) p (Cs ! i) \<and> \<not> (in_pos_cutset (N!i) p (Cs ! i)) "
by(simp add: cutset_vec_def)

lemma cutset_vec_index_negc_mone: "i < length Cs \<Longrightarrow> \<not> (in_pos_cutset (N!i) p (Cs ! i)) \<Longrightarrow> cutset_vec Cs p $ i = -1 \<longleftrightarrow> in_neg_cutset (N!i) p (Cs ! i)"
by(simp add: cutset_vec_def)

lemma cutset_vec_index_mone_alt: 
  assumes "i < length Cs" and "length N = length Cs" and  "(Cs!i) =  (cutset_edges (N!i))"
  shows  "cutset_vec Cs p $ i = -1 \<longleftrightarrow>  p \<in> set (Cs ! i) \<and>  p \<in> set (neg_cut_list (N!i))"
  using assms  neg_cutset_cond_indexed cutset_vec_index_mone_negc cutset_edges in_neg_cutset
  by (metis (no_types, lifting) in_pos_cutset neg_cut_not_pos notin_cutsets_not_pos_not_neg set_int2 wf_cutsets_sub wf_invalid_edge) 

lemma cutset_vec_index_one: "i < length Cs \<Longrightarrow> cutset_vec Cs p $ i = 1 \<longleftrightarrow> in_pos_cutset (N!i) p (Cs ! i) \<and> \<not> (in_neg_cutset (N!i) p (Cs ! i))"
     by(simp add: cutset_vec_def)

lemma cutset_vec_index_one_alt: 
  assumes "i < length Cs" and "length N = length Cs" and  "(Cs!i) = (cutset_edges (N!i))"
  shows "cutset_vec Cs p $ i = 1 \<longleftrightarrow> p \<in> set (Cs ! i) \<and>  p \<in> set (pos_cut_list (N!i))"
  using assms pos_cutset_altdef cutset_vec_index_one wf_invalid_cs wf_nonempty_netw_list_sys
  by (metis (no_types, lifting) cutset_edges neg_cut_not_pos neg_cutset_altdef nth_mem wf_invalid_edge)

lemma cutset_vec_index_zero: "i < length Cs \<Longrightarrow> cutset_vec Cs p $ i = 0 \<longleftrightarrow>
(in_pos_cutset (N!i) p (Cs ! i) \<and> in_neg_cutset (N!i) p (Cs ! i)) \<or> \<not> (in_neg_cutset (N!i) p (Cs ! i) \<or> in_pos_cutset (N!i) p (Cs ! i))"
     by(simp add: cutset_vec_def)

lemma cutset_vec_index_zero_alt: 
  assumes "i < length Cs" and "length N = length Cs" and  "(Cs!i) = (cutset_edges (N!i))"
  shows "cutset_vec Cs p $ i = 0 \<longleftrightarrow> (p \<in> set (pos_cut_list (N!i)) \<and> p \<in> set (neg_cut_list (N!i))) \<or> p \<notin> set (Cs ! i)"
  using assms cutset_vec_def cutset_vec_index_zero cut_list_pos_neg cutset_vec_index cutset_vec_index_mone_negc cutset_vec_index_mone_alt
  by (smt (z3) add.inverse_neutral cutset_vec_index_one_alt mem_Collect_eq neg_cut_not_pos cutset_edges_def nth_mem set_filter wf_nonempty_netw_list_sys)

lemma cutset_vec_index_zero_alt1: 
  assumes "i < length Cs" and "length N = length Cs" and  "(Cs!i) = (cutset_edges (N!i))"
  shows "cutset_vec Cs p $ i = 0 \<longleftrightarrow> p \<notin> set (Cs ! i)"
  using assms cutset_vec_def cutset_vec_index_zero_alt neg_cut_not_pos pos_cut_list_alt wf_nonempty_netw_list_sys by blast

text\<open>A cutset row vector is defined for a single cutset and edges that holds if an edge is in positive cutset then 1 else if it is in negative cutset then -1 else 0\<close>

definition cutset_rvec :: "'a nodes \<Rightarrow> 'a edges \<Rightarrow> 'a edges \<Rightarrow> ('b :: {field_char_0}) vec" where
"cutset_rvec u cs Es  \<equiv> vec (length Es) (\<lambda>j. if  \<not> (in_pos_cutset u (Es!j) cs) \<and> in_neg_cutset u (Es!j) cs then -1
        else if in_pos_cutset u (Es!j) cs \<and> \<not> (in_neg_cutset u (Es!j) cs)  then 1 else 0)"

lemma cutset_rvec_elems: "set\<^sub>v (cutset_rvec u cs Es) \<subseteq> {0, 1, -1}"
  by (auto simp add: vec_set_def cutset_rvec_def)

lemma finite_cutset_rvec: "finite (set\<^sub>v (cutset_rvec u cs Es))"
  by (auto simp add: vec_set_def cutset_rvec_def)

lemma cutset_rvec_dim: "dim_vec (cutset_rvec u cs Es) = length Es" by (simp add: cutset_rvec_def)

lemma cutset_rvec_index: "j < length Es \<Longrightarrow> cutset_rvec u cs Es $ j= (if  \<not> (in_pos_cutset u (Es!j) cs) \<and> in_neg_cutset u (Es!j) cs then -1
        else if in_pos_cutset u (Es!j) cs \<and> \<not> (in_neg_cutset u (Es!j) cs)  then 1  else 0)"
  by(simp add: cutset_rvec_def)

lemma cutset_rvec_index_mone: "j < length Es  \<Longrightarrow> cs = cutset_edges u \<Longrightarrow> (Es!j) \<notin> set (pos_cut_list u) \<Longrightarrow> cutset_rvec u cs Es $ j = -1  \<longleftrightarrow> (Es!j) \<in> set (neg_cut_list u) \<and> (Es ! j) \<in> set cs"
  using C\<^sub>n_def C\<^sub>p_def in_pos_cutset_def in_neg_cutset_def cutset_rvec_index neg_cutset_altdef pos_cutset_altdef
  by (metis (no_types, lifting) cutset_edges invalid_cut_pos_neg  wf_invalid_cs zero_neq_neg_one)


lemma cutset_rvec_index_one: "j < length Es  \<Longrightarrow> cs = cutset_edges u \<Longrightarrow> (Es!j) \<notin> set (neg_cut_list u) \<Longrightarrow> cutset_rvec u cs Es $ j = 1  \<longleftrightarrow> (Es!j) \<in> set (pos_cut_list u) \<and> (Es ! j) \<in> set cs"
 using in_pos_cutset_def in_neg_cutset_def
proof -
  assume a1: "Es ! j \<notin> set (neg_cut_list u)"
  assume a2: "cs = cutset_edges u"
  assume "j < length Es"
  then have a3: "nonempty_cutset_system \<N>s \<E>s \<C>s \<and> j < length Es"
    using nonempty_cutset_system_axioms by blast
  have a4: "u \<in> set N \<longrightarrow> cutset_edges u \<in> \<C>"
    using wf_2
    by (simp add: cutset_edges)
  have "\<not> in_neg_cutset u (Es ! j) cs \<or> Es ! j \<in> set (neg_cut_list u)"
    using neg_cutset_altdef by blast
  then have a5: "\<not> in_neg_cutset u (Es ! j) cs"
    using a1 by force
  have "Es ! j \<in> set cs \<or> \<not> in_pos_cutset u (Es ! j) cs"
    using notin_cutsets_not_pos_not_neg by blast
  then show ?thesis
    using a5 a4 a3 a2
    by (metis cutset_edges cutset_rvec_index nonempty_network_system.pos_cut_list_alt one_neq_zero pos_cutset_altdef wf_nonempty_netw_list_sys)
qed

lemma cutset_rvec_index_zero: "j < length Es  \<Longrightarrow> cs = cutset_edges u \<Longrightarrow> cutset_rvec u cs Es $ j = 0 \<longleftrightarrow> (Es ! j) \<notin> set cs "
  using C\<^sub>n_def C\<^sub>p_def in_pos_cutset_def in_neg_cutset_def cutset_rvec_index_mone cutset_rvec_index_one cutset_edges_def cutset_rvec_index wf_nonempty_netw_list_sys
  by (smt (verit, best) cut_list_pos_neg mem_Collect_eq neg_cut_not_pos neg_cutset_altdef one_neq_zero pos_cutset_altdef set_filter zero_neq_neg_one)


subsection \<open>Cutset Matrix\<close>

definition cutset_matrix :: "'a edges list \<Rightarrow> 'a edges \<Rightarrow> ('b :: {field_char_0}) mat" where
"cutset_matrix Cs Es \<equiv> mat (length Cs) (length Es) (\<lambda>(i,j). if \<not> (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> in_neg_cutset (N!i) (Es ! j) (Cs ! i) then -1
        else if in_pos_cutset (N!i) (Es ! j) (Cs ! i) \<and> \<not> in_neg_cutset (N!i) (Es ! j) (Cs ! i)  then 1 else 0)"

lemma cutset_matcol_dim: "dim_col (cutset_matrix Cs Es) = length Es" 
  by (simp add: cutset_matrix_def)

lemma cutset_matrow_dim: "dim_row (cutset_matrix Cs Es) = length Cs"   
  by (simp add: cutset_matrix_def)

lemma cutset_mat_elems: "elements_mat (cutset_matrix Cs Es) \<subseteq> {0, 1, -1}" 
  by (auto simp add: elements_mat_def cutset_matrix_def)

lemma finite_cutset_mat_elems: "finite (elements_mat (cutset_matrix Cs Es))"
  using finite_subset cutset_mat_elems by blast

lemma cutset_index[simp]: "i < size Cs \<Longrightarrow> j < size Es \<Longrightarrow> 
cutset_matrix Cs Es  = mat (size Cs) (size Es) (\<lambda>(i,j). if \<not> (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> in_neg_cutset (N!i) (Es ! j) (Cs ! i) then -1
        else if in_pos_cutset (N!i) (Es ! j) (Cs ! i) \<and> \<not> in_neg_cutset (N!i) (Es ! j) (Cs ! i) then 1 else 0)"
  unfolding cutset_matrix_def by blast

lemma cutset_matrix_edge_in_csneg_mone: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow>
 \<not> (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> in_neg_cutset (N!i) (Es ! j) (Cs ! i)
    \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = -1"
  by (simp add: cutset_matrix_def)

lemma cutset_matrix_edge_in_csneg_mone_alt:
  assumes "(Cs!i) = (cutset_edges (N!i))"
  shows "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow>
  (Es!j) \<in> set (Cs ! i) \<and> (Es!j) \<in> set (neg_cut_list (N!i))
    \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = -1"
  unfolding cutset_matrix_def using  wf_nonempty_netw_list_sys neg_cutset_altdef neg_cut_list_alt
      assms cutset_edges in_pos_cutset pos_cut_not_neg wf_2 by auto

lemma cutset_matrix_edge_in_cspos_one: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow>
 (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> \<not> in_neg_cutset (N!i) (Es ! j) (Cs ! i)
    \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = 1"
 by (simp add: cutset_matrix_def)

lemma cutset_matrix_edge_in_cspos_one_alt:
  assumes "(Cs!i) = (cutset_edges (N!i))"
  shows "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow>
  (Es!j) \<in> set (Cs ! i) \<and> (Es!j) \<in> set (pos_cut_list (N!i))
    \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = 1"
  unfolding cutset_matrix_def using assms 
  by (smt (verit, del_insts) case_prod_conv cutset_rvec_index cutset_rvec_index_one index_mat(1) neg_cut_not_pos)

lemma cutset_matrix_edge_notin_cs_zero: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow>
  (\<not> ((in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<or> in_neg_cutset (N!i) (Es ! j) (Cs ! i)))
    \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = 0"
 by (simp add: cutset_matrix_def)

lemma cutset_matrix_edge_notin_cs_zero_alt: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow>
  (Es!j) \<notin> set (Cs ! i) 
    \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = 0"
 using  cut_list_pos_neg 
 by (metis cutset_matrix_edge_notin_cs_zero neg_cutset_altdef pos_cutset_altdef)

lemma cutset_matrix_edge_notin_cs_zero_1: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow>
  (((in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> in_neg_cutset (N!i) (Es ! j) (Cs ! i)))
    \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = 0"
 by (simp add: cutset_matrix_def)

lemma cutset_matrix_edge_notin_cs_zero_1_alt: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow>
  (Es!j) \<notin> set (Cs ! i) \<or> ((Es!j) \<notin> set (pos_cut_list (N!i)) \<and> (Es!j) \<notin> set (neg_cut_list (N!i)))
    \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = 0"
  using cut_list_pos_neg cut_list_def
  by (meson cutset_matrix_edge_notin_cs_zero neg_cutset_altdef in_neg_cutset_def in_pos_cutset_def nonempty_cutset_system_axioms pos_cutset_altdef)

lemma cutset_matrix_edge_in_csneg: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = -1 
\<Longrightarrow> \<not> (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> in_neg_cutset (N!i) (Es ! j) (Cs ! i)"
  using cutset_matrix_edge_notin_cs_zero cutset_matrix_edge_in_cspos_one
  by (metis neg_cutset_altdef neg_cut_not_pos one_neq_neg_one pos_cutset_altdef zero_neq_neg_one)

lemma cutset_matrix_edge_in_cspos: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = 1 
\<Longrightarrow> (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> \<not> in_neg_cutset (N!i) (Es ! j) (Cs ! i)"
  using cutset_matrix_edge_notin_cs_zero cutset_matrix_edge_in_csneg_mone
  by (metis cutset_matrix_edge_notin_cs_zero_1 cutset_vec_index cutset_vec_index_one)

lemma cutset_matrix_edge_notin_cs: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = 0
\<Longrightarrow> \<not> (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> \<not> in_neg_cutset (N!i) (Es ! j) (Cs ! i)"
  using cutset_matrix_edge_in_cspos_one cutset_matrix_edge_in_csneg_mone 
  by (metis neg_cutset_altdef neg_cut_not_pos one_neq_zero pos_cutset_altdef zero_neq_neg_one)

lemma cutset_matrix_edge_notin_cs_1: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = 0
\<Longrightarrow> ((in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> in_neg_cutset (N!i) (Es ! j) (Cs ! i)) \<or> 
(\<not> (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> \<not> in_neg_cutset (N!i) (Es ! j) (Cs ! i))"
  by (metis cutset_matrix_edge_notin_cs)

lemma cutset_matrix_edge_in_csneg_iff: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow> (cutset_matrix Cs Es) $$ (i, j) = -1 
\<longleftrightarrow> \<not> (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> in_neg_cutset (N!i) (Es ! j) (Cs ! i)"
  by (meson cutset_matrix_edge_in_csneg cutset_matrix_edge_in_csneg_mone)

lemma cutset_matrix_edge_in_cspos_iff: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow> 
(cutset_matrix Cs Es) $$ (i, j) = 1 \<longleftrightarrow> (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> \<not> in_neg_cutset (N!i) (Es ! j) (Cs ! i)"
  by (meson cutset_matrix_edge_in_cspos cutset_matrix_edge_in_cspos_one)

lemma cutset_matrix_edge_notin_cs_iff: "i < length Cs \<Longrightarrow> j < length Es \<Longrightarrow> 
(cutset_matrix Cs Es) $$ (i, j) = 0 \<longleftrightarrow> \<not> (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> \<not> in_neg_cutset (N!i) (Es ! j) (Cs ! i)"
  by (metis cutset_matrix_edge_notin_cs cutset_matrix_edge_notin_cs_zero)

text \<open>Reasoning on Columns/Rows of the cutset matrix\<close>

lemma cutset_matrix_col_def:  "j < length Es \<Longrightarrow> i < length Cs \<Longrightarrow> 
    (col (cutset_matrix Cs Es) j) $ i = (if \<not> (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> in_neg_cutset (N!i) (Es ! j) (Cs ! i) then -1
        else if in_pos_cutset (N!i) (Es ! j) (Cs ! i) \<and> \<not> in_neg_cutset (N!i) (Es ! j) (Cs ! i) then 1 else 0)"
  by (simp add: cutset_matrix_def)

lemma cutset_mat_col_list_map_elem: "j < length Es \<Longrightarrow> i < length Cs \<Longrightarrow>
    col (cutset_matrix Cs Es) j $ i = map_vec 
    (\<lambda> x . if  \<not> (in_pos_cutset (N!i) (Es ! j) x ) \<and> in_neg_cutset (N!i) (Es ! j) x then -1
        else if in_pos_cutset (N!i) (Es ! j) x \<and> \<not> in_neg_cutset (N!i) (Es ! j) x then 1 else 0) (vec_of_list Cs) $ i"
 by (simp add: cutset_matrix_col_def vec_of_list_index)

lemma cutset_matrix_row_def:  "j < length Es \<Longrightarrow> i < length Cs \<Longrightarrow> 
    (row (cutset_matrix Cs Es) i) $ j = (if \<not> (in_pos_cutset (N!i) (Es ! j) (Cs ! i)) \<and> in_neg_cutset (N!i) (Es ! j) (Cs ! i) then -1
        else if in_pos_cutset (N!i) (Es ! j) (Cs ! i) \<and> \<not> in_neg_cutset (N!i) (Es ! j) (Cs ! i) then 1 else 0)"
  by (simp add: cutset_matrix_def)

lemma cutset_mat_row_list_map_elem: "j < length Es \<Longrightarrow> i < length Cs \<Longrightarrow>
    row (cutset_matrix Cs Es) i $ j = map_vec 
    (\<lambda> b . if \<not> (in_pos_cutset (N!i) b (Cs ! i)) \<and> in_neg_cutset (N!i) b (Cs ! i) then -1
        else if in_pos_cutset (N!i) b (Cs ! i) \<and> \<not> in_neg_cutset (N!i) b (Cs ! i) then 1 else 0) (vec_of_list Es) $ j"
  by (simp add: cutset_matrix_col_def vec_of_list_index)

text \<open>Connection between the cutset vector and the cutset matrix\<close>

lemma cutset_colmat_cutset_vec: " j < length Es \<Longrightarrow>  col (cutset_matrix Cs Es) j = cutset_vec Cs (Es ! j)"
  by (auto simp add: cutset_matrix_def cutset_vec_def)

lemma cutset_colsmat_cutset_vec:
  shows "cols (cutset_matrix Cs Es) = map (\<lambda> j. cutset_vec Cs j) Es"
proof(intro nth_equalityI)
 have c1: "length (cols (cutset_matrix Cs Es)) = length (map (cutset_vec Cs) Es)"
    using cutset_matcol_dim by simp
  have c2: "length (map (\<lambda> j. cutset_vec Cs j) Es) = length Es"
    using length_map by simp
  then show "length (cols (cutset_matrix Cs Es)) = length (map (cutset_vec Cs) Es)"
    using c1 c2 by auto
  show "\<And>i. i < length (cols (cutset_matrix Cs Es)) \<Longrightarrow> cols (cutset_matrix Cs Es) ! i = map (cutset_vec Cs) Es ! i "
    by (auto simp add: cutset_colmat_cutset_vec cutset_matcol_dim)
qed

lemma cutset_rowmat_cutset_rvec: "i < length Cs \<Longrightarrow>  Cs!i = cutset_edges (N!i) \<Longrightarrow> row (cutset_matrix Cs Es) i = cutset_rvec (N!i) (Cs!i) Es"
 by (auto simp add: cutset_matrix_def cutset_rvec_def)


abbreviation  B :: "real mat" where
"B \<equiv> cutset_matrix \<C>s \<E>s"

lemma B_alt_def: "B = mat z n (\<lambda> (i,j). 
if \<not> (in_pos_cutset (N!i) (\<E>s ! j) (\<C>s ! i)) \<and> in_neg_cutset (N!i) (\<E>s ! j) (\<C>s ! i) then -1
        else if in_pos_cutset (N!i) (\<E>s ! j) (\<C>s ! i) \<and> \<not> in_neg_cutset (N!i) (\<E>s ! j) (\<C>s ! i) then 1 else 0)"
  using cutset_matrix_def by blast

lemma inpos_cuts_B_one: "i < z \<Longrightarrow> j < n \<Longrightarrow> in_pos_cutset (N!i) (\<E>s ! j) (\<C>s ! i) \<and> \<not> in_neg_cutset (N!i) (\<E>s ! j) (\<C>s ! i) \<Longrightarrow> B $$ (i, j) = 1" 
  using B_alt_def cutset_matrix_edge_in_cspos_iff by blast
 
lemma inneg_cuts_B_mone: "i < z \<Longrightarrow> j < n \<Longrightarrow> \<not> (in_pos_cutset (N!i) (\<E>s ! j) (\<C>s ! i)) \<and> in_neg_cutset (N!i) (\<E>s ! j) (\<C>s ! i) \<Longrightarrow> B $$ (i, j) = -1"
 using B_alt_def cutset_matrix_edge_in_csneg_iff by blast

lemma notin_cuts_B_zero: "i < z \<Longrightarrow> j < n \<Longrightarrow> \<not> (in_pos_cutset (N!i) (\<E>s ! j) (\<C>s ! i)) \<and> \<not> in_neg_cutset (N!i) (\<E>s ! j) (\<C>s ! i) \<Longrightarrow> B $$ (i, j) = 0"
 using B_alt_def cutset_matrix_edge_notin_cs by simp

text \<open>Matrix Dimension related lemmas \<close>
 
lemma B_carrier_mat: "B \<in> carrier_mat z n" 
  by (simp add: cutset_matrix_def)

lemma dim_row_is_z[simp]: "dim_row B = z"
  using B_carrier_mat by blast

lemma dim_col_is_n[simp]: "dim_col B = n"
  using  cutset_matcol_dim  by (simp add: cutset_matrix_def)

lemma dim_vec_row_B: "dim_vec (row B i) = n"
  by simp

lemma dim_vec_col_B: "dim_vec (col B i) = z"
  by simp 

lemma dim_vec_z_col: 
  assumes "j < n"
  shows "dim_vec (cols B ! j) = z"
  using assms by simp

lemma B_elems: "elements_mat B \<subseteq> {0, 1, -1}"
  by (auto simp add: cutset_matrix_def elements_mat_def)

lemma B_finite: "finite (elements_mat B)"
  by(simp add: finite_cutset_mat_elems)

lemma B_elems_max_3: "card (elements_mat B) \<le> 3"
  using B_alt_def numeral_3_eq_3 B_elems 
  by (smt (verit, best) card.empty card_insert_disjoint card_mono finite.emptyI finite_insert insert_absorb insert_iff insert_not_empty)

text \<open>Transpose properties \<close>

lemma B_trans_index_val: "i < dim_col B \<Longrightarrow> j < dim_row B \<Longrightarrow> 
    B\<^sup>T $$ (i, j) = (if \<not> (in_pos_cutset (N!j) (\<E>s ! i) (\<C>s ! j)) \<and> in_neg_cutset (N!j) (\<E>s ! i) (\<C>s ! j) then -1 
else if in_pos_cutset (N!j) (\<E>s ! i) (\<C>s ! j) \<and> \<not> (in_neg_cutset (N!j) (\<E>s ! i) (\<C>s ! j)) then 1 else 0)"
  using B_alt_def by auto

lemma transpose_entries: "elements_mat (B\<^sup>T) \<subseteq> {0, 1, -1}"
  using B_trans_index_val  by (metis B_elems transpose_mat_elems)

text \<open>Cutset Matrix elements and index related lemmas \<close>

lemma B_mat_row_elems: "i < z \<Longrightarrow> vec_set (row B i) \<subseteq> {0, 1, -1}"
  by (metis B_elems dim_row_is_z row_elems_subset_mat subset_trans)

lemma B_mat_col_elems: "j < n \<Longrightarrow> vec_set (col B j) \<subseteq> {0, 1, -1}"
  using dim_col_is_n by (metis B_elems col_elems_subset_mat subset_trans)

lemma B_matrix_elems_one_mone_zero: "i < z \<Longrightarrow> j < n \<Longrightarrow> B $$ (i, j) = 0 \<or> B $$ (i, j) = 1 \<or> B $$ (i, j) = -1" 
  by (simp add: cutset_matrix_def)

lemma B_matrix_not_zero[simp]: "i < z \<Longrightarrow> j < n \<Longrightarrow> B $$ (i, j) \<noteq> 0 \<Longrightarrow>  B $$ (i, j) = 1 \<or> B $$ (i, j) = -1" 
  using B_matrix_elems_one_mone_zero by blast

lemma B_matrix_not_one[simp]: "i < z \<Longrightarrow> j < n \<Longrightarrow> B $$ (i, j) \<noteq> 1 \<Longrightarrow>  B $$ (i, j) = 0 \<or> B $$ (i, j) = -1" 
  using B_matrix_elems_one_mone_zero by blast

lemma B_matrix_not_mone[simp]: "i < z \<Longrightarrow> j < n \<Longrightarrow> B $$ (i, j) \<noteq> -1 \<Longrightarrow>  B $$ (i, j) = 1 \<or> B $$ (i, j) = 0" 
  using B_matrix_not_one by blast

lemma B_matrix_not_mone_not_one: "i < z \<Longrightarrow> j < n \<Longrightarrow> B $$ (i, j) \<noteq> -1 \<Longrightarrow>  B $$ (i, j) \<noteq> 1 \<Longrightarrow> B $$ (i, j) = 0" 
  using B_matrix_not_one B_matrix_not_mone by blast

lemma B_matrix_not_mone_not_zero: "i < z \<Longrightarrow> j < n \<Longrightarrow> B $$ (i, j) \<noteq> -1 \<Longrightarrow>  B $$ (i, j) \<noteq> 0 \<Longrightarrow> B $$ (i, j) = 1" 
  using B_matrix_elems_one_mone_zero by blast

lemma B_matrix_not_one_not_zero: "i < z \<Longrightarrow> j < n \<Longrightarrow> B $$ (i, j) \<noteq> 1 \<Longrightarrow>  B $$ (i, j) \<noteq> 0 \<Longrightarrow> B $$ (i, j) = -1" 
  using B_matrix_not_mone_not_one nonempty_cutset_system_axioms by blast

lemma B_index_square_itself: "j < dim_col B \<Longrightarrow> i < dim_row B \<Longrightarrow> (B $$ (i, j))^2 = abs (B $$ (i, j))"
  by simp

lemma B_matrix_edge_in_negcutset: "i < z \<Longrightarrow> j < n  
\<Longrightarrow> B $$ (i, j) = -1  \<Longrightarrow> (\<E>s ! j) \<in> set (\<C>s ! i) \<Longrightarrow>  (\<E>s ! j) \<in> set (neg_cut_list (N!i))"
  using B_alt_def dim_row_is_z dim_col_is_n
  by (smt (verit) B_trans_index_val index_transpose_mat(1) neg_cutset_altdef in_neg_cutset_def nonempty_cutset_system_axioms)

lemma B_matrix_edge_in_poscutset: "i < z \<Longrightarrow> j < n
\<Longrightarrow>  B $$ (i, j) = 1 \<Longrightarrow>  (\<E>s ! j) \<in> set (\<C>s ! i) \<and>  (\<E>s ! j) \<in> set (pos_cut_list (N!i))"
  using B_alt_def  dim_row_is_z dim_col_is_n
  by (smt (verit, ccfv_SIG) in_pos_cutset_def index_mat(1) old.prod.case pos_cutset_altdef)
  
lemma B_matrix_edge_notin_cutset: "i < z \<Longrightarrow> j < n \<Longrightarrow> (\<C>s!i) = (cutset_edges (N!i)) \<Longrightarrow> B $$ (i, j) = 0
\<Longrightarrow> (\<E>s ! j) \<notin> set (\<C>s ! i) "
  using nonempty_cutset_system.cutset_matrix_edge_notin_cs_iff 
 nonempty_cutset_system_axioms not_pos_nor_neg_ntin_cuts_cond_indexed 
  by (metis cutset_edges)

lemma B_matrix_edge_in_poscutset_iff: "i < z \<Longrightarrow> j < n \<Longrightarrow> (\<C>s!i) = (cutset_edges (N!i)) \<Longrightarrow>
B $$ (i, j) = 1 \<longleftrightarrow> (\<E>s ! j) \<in> set (\<C>s ! i) \<and>  (\<E>s ! j) \<in> set (pos_cut_list (N!i))"
  using B_matrix_edge_in_poscutset cutset_matrix_edge_in_cspos_one_alt oops

lemma B_matrix_edge_in_negcutset_iff: "i < z \<Longrightarrow> j < n \<Longrightarrow> (\<C>s!i) = (cutset_edges (N!i))  \<Longrightarrow> B $$ (i, j) = -1 \<longleftrightarrow> (\<E>s ! j) \<in> set (\<C>s ! i) \<and> (\<E>s ! j) \<in> set (neg_cut_list (N!i))"
  using B_matrix_edge_in_negcutset
  by (meson cutset_matrix_edge_in_csneg cutset_matrix_edge_in_csneg_mone_alt neg_cutset_altdef)

lemma B_matrix_edge_notin_cutset_iff: "i < z \<Longrightarrow> j < n  \<Longrightarrow> (\<C>s!i) = (cutset_edges (N!i)) \<Longrightarrow> B $$ (i, j) = 0
\<Longrightarrow>  (\<E>s ! j) \<notin> set (\<C>s ! i) "
  using B_matrix_edge_notin_cutset by blast

text \<open>A cutset vector is a column of the cutset matrix\<close>

lemma col_cutset_vec: "j < length \<E>s \<Longrightarrow> cutset_vec \<C>s (\<E>s ! j) = col B j"
  by (simp add: cutset_colmat_cutset_vec) 

text \<open>A cutset row vector is equal to the row of the cutset matrix\<close>

lemma row_cutset_rvec: "i < length \<C>s \<Longrightarrow> cutset_rvec (N!i) (\<C>s ! i) \<E>s = row B i"
  using cutset_rowmat_cutset_rvec B_alt_def
  by (smt (verit, ccfv_SIG) cutset_matrix_row_def cutset_rvec_dim cutset_rvec_index dim_vec_row_B eq_vecI)

text \<open>Degree of the each row of the cutset matrix is equal to the number of nonzero elements of each row\<close>

lemma cutset_mat_degree: "i < length  \<C>s \<Longrightarrow> of_nat (mat_degree_num B i) = sum_abs_vec (row B i)"
  unfolding mat_degree_num_def mat_in_degree_num_def mat_out_degree_num_def 
  by (metis B_mat_row_elems add.commute count_abs_vec1_sum_non_zero_elems_alt)

end
end

