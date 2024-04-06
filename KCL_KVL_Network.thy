theory KCL_KVL_Network
  imports  Loop_Matrix
begin 

text\<open>Formalization of KCL and KVL\<close>

definition KCL :: "(real \<Rightarrow> real) list \<Rightarrow> real \<Rightarrow> bool" where 
  "KCL Is t \<equiv> ((\<Sum>i\<in>{0..<length Is}. (Is!i) t) = 0)"

definition KVL :: "(real \<Rightarrow> real) list \<Rightarrow> real \<Rightarrow> bool" where 
  "KVL Vs t \<equiv> ((\<Sum>i\<in>{0..<length Vs}. (Vs!i) t) = 0)"

definition vecc :: "(real \<Rightarrow> real) list \<Rightarrow> real \<Rightarrow> real vec"
  where "vecc Is t = vec (length Is) (\<lambda>i. (Is!i) t)"

lemma vecc_carrier[simp]:
  "vecc Is t \<in> carrier_vec (length Is)"
  unfolding vecc_def by auto

lemma index_curr_vec[simp]:
  shows "i < length Is \<Longrightarrow> (vecc Is t) $ i = (Is ! i) t"
  unfolding vecc_def by auto

lemma dimvec_curr_len: "dim_vec (vecc Is t) = length Is"
    by auto

lemma numeral_4_eq_4: "4 = Suc (Suc (Suc (Suc 0)))"
  by (simp add: eval_nat_numeral)

lemma numeral_5_eq_5: "5 = Suc (Suc (Suc (Suc (Suc 0))))"
  by (simp add: eval_nat_numeral)

lemma curr_vec_open: "vecc ([I0, I1, I2, I3, I4, I5]) t = vec_of_list [I0 t, I1 t, I2 t, I3 t, I4 t, I5 t]" (is "?L =?R") 
proof
  let ?is = "[I0, I1, I2, I3, I4, I5]"
  let ?ist = "[I0 t, I1 t, I2 t, I3 t, I4 t, I5 t]"
  show "dim_vec (vecc ?is t) = dim_vec (vec_of_list ?ist)"
    using dimvec_curr_len[of ?is t] dim_vec_of_list[of ?ist] by simp
  show "\<And>i. i < dim_vec (vec_of_list ?ist) \<Longrightarrow>vecc ?is t $ i = vec_of_list ?ist $ i  "
  proof-
    fix i assume ii: "i<dim_vec (vec_of_list ?ist)"
    show "vecc ?is t $ i = vec_of_list ?ist $ i " 
    proof-
      have 1: "vecc ?is t $ i = (?is ! i) t"
        using index_curr_vec ii by auto
      have "vecc ?is t $ 0 = I0 t"
        using 1 ii by auto
      moreover have "vec_of_list ?ist $ 0 = I0 t"
        by auto
      then have c0: "vecc ?is t $ 0 = vec_of_list ?ist $ 0"
        by auto
      have "vecc ?is t $ 1 = I1 t"
        using 1 ii by auto
      moreover have "vec_of_list ?ist $ 1 = I1 t"
        by auto
      then have c1: "vecc ?is t $ 1 = vec_of_list ?ist $ 1"
        by auto
      have "vecc ?is t $ 2 = I2 t"
        using 1 ii by auto
      moreover have "vec_of_list ?ist $ 2 = I2 t"
        by (simp add: numeral_2_eq_2)
      then have c2: "vecc ?is t $ 2 = vec_of_list ?ist $ 2"
        by auto
      have "vecc ?is t $ 3 = I3 t"
        using 1 ii by auto
      moreover have "vec_of_list ?ist $ 3 = I3 t"
        by (simp add: numeral_3_eq_3)
      then have c3: "vecc ?is t $ 3 = vec_of_list ?ist $ 3"
        by auto
      have "vecc ?is t $ 4 = I4 t"
        using 1 ii by auto
      moreover have "vec_of_list ?ist $ 4 = I4 t"
        by (simp add: numeral_4_eq_4)
      then have c4: "vecc ?is t $ 4 = vec_of_list ?ist $ 4"
        by auto
      have "vecc ?is t $ 5 = I5 t"
        using 1 ii by auto
      moreover have "vec_of_list ?ist $ 5 = I5 t"
        by (simp add: numeral_5_eq_5)
      then have "vecc ?is t $ 5 = vec_of_list ?ist $ 5"
        by auto
      thus ?thesis using c4 c3 c2 c1 c0 ii less_Suc_eq numeral_2_eq_2 by fastforce
    qed
  qed
qed

definition circuit_mat_imp  where 
    "circuit_mat_imp A Is t \<equiv> ((A *\<^sub>v (vecc Is t)) = 0\<^sub>v (dim_row A))"

lemma KCL_mat_imp: 
  assumes "circuit_mat_imp A Is t" 
  assumes "i< dim_row A"
  shows "(A *\<^sub>v (vecc Is t))$i = 0\<^sub>v (dim_row A) $ i"
proof-
  have "((A *\<^sub>v (vecc Is t)) = 0\<^sub>v (dim_row A))"
    using assms(1) circuit_mat_imp_def by auto
  thus ?thesis using assms(2) by auto
qed

text \<open>KCL circuit analysis via incidence matrix\<close>

context nonempty_loop_system
begin

definition KCL_imp :: "(real \<Rightarrow> real) list \<Rightarrow> real \<Rightarrow> bool"  where 
    "KCL_imp Is t \<equiv> KCL [Is!1, Is!2, -(Is!0)] t \<and> 
                    KCL [Is!4, -(Is!1), -(Is!3)] t \<and> 
                    KCL [Is!3, (Is!5), -(Is!2)] t \<and> 
                    KCL [Is!0, -(Is!4), -(Is!5)] t"

lemma kcl_circ_eqs: "KCL_imp Is t \<longleftrightarrow> (Is!1) t + (Is!2) t = (Is!0) t  
                                      \<and> (Is!1) t + (Is!3) t = (Is!4) t  
                                      \<and> (Is!3) t + (Is!5) t = (Is!2) t
                                      \<and> (Is!4) t + (Is!5) t = (Is!0) t"
  unfolding KCL_imp_def KCL_def by auto

text\<open>Verification of incidence matrix of the RLC circuit\<close>
lemma incidence_matrix_rlc: 
  assumes "\<N>s = [n1::'a, n2, n3, n4]" "\<E>s = [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]"
  shows "(incidence_matrix \<N>s \<E>s ::real mat)= mat_of_rows_list 6 [[-1::real, 1, 1, 0 , 0, 0], [0::real, -1, 0, -1, 1, 0],
                                [0::real, 0, -1, 1, 0, 1], [1::real, 0, 0, 0, -1, -1]] " (is "_=?rhs")  
  proof(rule eq_matI)
  show  c1: "dim_row K = dim_row ?rhs" 
    using assms distincts dim_row_K by auto 
  show c2: "dim_col K = dim_col ?rhs" 
 using assms distincts dim_col_K by auto
  show "\<And>i j. i <dim_row ?rhs \<Longrightarrow>
           j < dim_col ?rhs \<Longrightarrow> K $$ (i, j) = ?rhs $$ (i, j)"
  proof-
 have 1: "dim_row K = 4"  using dim_row_K assms(1) by auto
 have posincs: "pos_incident (\<N>s!0) (\<E>s!1)" "pos_incident (\<N>s!0) (\<E>s!2)" "pos_incident (\<N>s!1) (\<E>s!4)"
                "pos_incident (\<N>s!2) (\<E>s!3)" "pos_incident (\<N>s!2) (\<E>s!5)"  "pos_incident (\<N>s!3) (\<E>s!0)" 
  using assms pos_incident_netw_altdef  by auto
 have negincs: "neg_incident (\<N>s!0) (\<E>s!0)"  "neg_incident (\<N>s!1) (\<E>s!1)"  "neg_incident (\<N>s!1) (\<E>s!3)" 
                 "neg_incident (\<N>s!2) (\<E>s!2)"  "neg_incident (\<N>s!3) (\<E>s!4)"  "neg_incident (\<N>s!3) (\<E>s!5)" 
    using assms neg_incident_netw_altdef by auto 
  have notincs: "\<not> pos_incident (\<N>s!1) (\<E>s!0) \<and> \<not> neg_incident (\<N>s!1) (\<E>s!0)" "\<not> pos_incident (\<N>s!0) (\<E>s!3) \<and> \<not> neg_incident (\<N>s!0) (\<E>s!3)" 
      "\<not> pos_incident (\<N>s!0) (\<E>s!4) \<and> \<not> neg_incident (\<N>s!0) (\<E>s!4)" "\<not> pos_incident (\<N>s!0) (\<E>s!5) \<and> \<not> neg_incident (\<N>s!0) (\<E>s!5)"
     "\<not> pos_incident (\<N>s!1) (\<E>s!2) \<and> \<not> neg_incident (\<N>s!1) (\<E>s!2)" "\<not> pos_incident (\<N>s!1) (\<E>s!5) \<and> \<not> neg_incident (\<N>s!1) (\<E>s!5)"
      "\<not> pos_incident (\<N>s!2) (\<E>s!0) \<and> \<not> neg_incident (\<N>s!2) (\<E>s!0)" "\<not> pos_incident (\<N>s!2) (\<E>s!1) \<and> \<not> neg_incident (\<N>s!2) (\<E>s!1)"
      "\<not> pos_incident (\<N>s!2) (\<E>s!4) \<and> \<not> neg_incident (\<N>s!2) (\<E>s!4)" "\<not> pos_incident (\<N>s!3) (\<E>s!1) \<and> \<not> neg_incident (\<N>s!3) (\<E>s!1)" 
      "\<not> pos_incident (\<N>s!3) (\<E>s!2) \<and> \<not> neg_incident (\<N>s!3) (\<E>s!2)" "\<not> pos_incident (\<N>s!3) (\<E>s!3) \<and> \<not> neg_incident (\<N>s!3) (\<E>s!3)" 
    using assms not_pos_not_neg_incident_netw distincts by auto
  fix i j assume i: "i < dim_row (?rhs)" and j: " j < dim_col (?rhs)"
  have r00: "K $$ (0, 0) = ?rhs $$ (0, 0)"
      using negincs(1) neg_inc_K_mone i j c1 c2 by (simp add: mat_of_rows_list_def)      
  moreover have r01: "K $$ (0, 1) = ?rhs $$ (0, 1)"
      using i j posincs(1) c1 c2 pos_inc_K_one by (simp add: mat_of_rows_list_def)
    moreover have r02: "K $$ (0, 2) = ?rhs $$ (0, 2)"
      using i j posincs(2) c1 c2 pos_inc_K_one by (simp add: mat_of_rows_list_def)
    moreover have r03: "K $$ (0, 3) = ?rhs $$ (0, 3)"
       using i j notincs(2) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)      
    moreover have r04: "K $$ (0, 4) = ?rhs $$ (0, 4)"
       using i j notincs(3) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)      
    moreover have r05: "K $$ (0, 5) = ?rhs $$ (0, 5)"
       using i j notincs(4) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def) 
    moreover have r10: "K $$ (1, 0) = ?rhs $$ (1, 0)" 
       using i j notincs(1) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)    
    moreover have r11: "K $$ (1, 1) = ?rhs $$ (1, 1)"    
      using i j negincs(2) c1 c2 neg_inc_K_mone by (simp add: mat_of_rows_list_def) 
    moreover have r12: "K $$ (1, 2) = ?rhs $$ (1, 2)" 
       using i j notincs(5) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)   
    moreover have r13: "K $$ (1, 3) = ?rhs $$ (1, 3)" 
       using i j negincs(3) c1 c2 neg_inc_K_mone by (simp add: mat_of_rows_list_def) 
    moreover have r14: "K $$ (1, 4) = ?rhs $$ (1, 4)" 
       using i j posincs(3) c1 c2 pos_inc_K_one by (simp add: mat_of_rows_list_def)
    then have r15: "K $$ (1, 5) = ?rhs $$ (1, 5)" 
       using i j notincs(6) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def) 
    moreover have r20: "K $$ (2, 0) = ?rhs $$ (2, 0)" 
       using i j notincs(7) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def) 
    moreover have r21: "K $$ (2, 1) = ?rhs $$ (2, 1)" 
       using i j notincs(8) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def) 
    moreover have r22: "K $$ (2, 2) = ?rhs $$ (2, 2)"
      using i j negincs(4) c1 c2 neg_inc_K_mone by (simp add: mat_of_rows_list_def)
    moreover have r23: "K $$ (2, 3) = ?rhs $$ (2, 3)" 
      using i j posincs(4) c1 c2 pos_inc_K_one by (simp add: mat_of_rows_list_def)
    moreover have r24: "K $$ (2, 4) = ?rhs $$ (2, 4)"  
      using i j notincs(9) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)
    moreover have r25: "K $$ (2, 5) = ?rhs $$ (2, 5)" 
      using i j posincs(5) c1 c2 pos_inc_K_one by (simp add: mat_of_rows_list_def)
    moreover have r30: "K $$ (3, 0) = ?rhs $$ (3, 0)" 
      using i j posincs(6) c1 c2 pos_inc_K_one by (simp add: mat_of_rows_list_def)
    moreover have r31: "K $$ (3, 1) = ?rhs $$ (3, 1)"
      using i j notincs(10) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)   
    moreover have r32: "K $$ (3, 2) = ?rhs $$ (3, 2)" 
      using i j notincs(11) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)
    moreover have r33: "K $$ (3, 3) = ?rhs $$ (3, 3)"
      using i j notincs(12) c1 c2 no_inc_K_zero by (simp add: mat_of_rows_list_def)
    moreover have r34: "K $$ (3, 4) = ?rhs $$ (3, 4)"
      using i j negincs(5) c1 c2 neg_inc_K_mone by (simp add: mat_of_rows_list_def)
    moreover have r35: "K $$ (3, 5) = ?rhs $$ (3, 5)"
      using i j negincs(6) c1 c2 neg_inc_K_mone by (simp add: mat_of_rows_list_def)
    ultimately show " K $$ (i, j) = ?rhs $$ (i, j)"
      using i j c1 
      by (smt (z3) "1" One_nat_def Suc_numeral c1 less_2_cases_iff 
          less_SucE matrl_carrier(3) numeral_3_eq_3 numeral_4_eq_4 
                            r14 semiring_norm(5) semiring_norm(8))      
  qed
qed

lemma inci_rows_list: "i < length [[-1::real, 1, 1, 0 , 0, 0], [0::real, -1, 0, -1, 1, 0],[0::real, 0, -1, 1, 0, 1], [1::real, 0, 0, 0, -1, -1]] \<Longrightarrow>  
length ([[-1::real, 1, 1, 0 , 0, 0], [0::real, -1, 0, -1, 1, 0],[0::real, 0, -1, 1, 0, 1], [1::real, 0, 0, 0, -1, -1]]!i) = 6"
  by (simp add: nth_Cons')

lemma lhs_K_inci: 
  assumes "i < length [[-1::real, 1, 1, 0 , 0, 0], [0::real, -1, 0, -1, 1, 0],[0::real, 0, -1, 1, 0, 1], [1::real, 0, 0, 0, -1, -1]]"
  shows "(row (mat_of_rows_list 6 [[-1::real, 1, 1, 0 , 0, 0], [0::real, -1, 0, -1, 1, 0],
                             [0::real, 0, -1, 1, 0, 1], [1::real, 0, 0, 0, -1, -1]]) i) = vec_of_list ([[-1::real, 1, 1, 0 , 0, 0], [0::real, -1, 0, -1, 1, 0],
                             [0::real, 0, -1, 1, 0, 1], [1::real, 0, 0, 0, -1, -1]]!i) "
  using assms inci_rows_list row_mat_of_rows_list by blast

lemma Kinci_rowseq: 
assumes "\<N>s = [n1::'a, n2, n3, n4]" "\<E>s = [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]"
shows "(row K 0) = vec_of_list [-1::real, 1, 1, 0 , 0, 0]"
      "(row K 1) = vec_of_list [0::real, -1, 0, -1, 1, 0]"
      "(row K 2) = vec_of_list [0::real, 0, -1, 1, 0, 1]"
      "(row K 3) = vec_of_list [1::real, 0, 0, 0, -1, -1]"
using lhs_K_inci incidence_matrix_rlc assms  by auto

text\<open>Implementation of KCL via incidence matrix\<close>
lemma KCL_inci_mat_imp: 
assumes "\<N>s = [n1::'a, n2, n3, n4]" "\<E>s = [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]"
shows "circuit_mat_imp (incidence_matrix \<N>s \<E>s) [Is!0, Is!1, Is!2, Is!3, Is!4, Is!5] t \<Longrightarrow>
                                                                          (Is!1) t + (Is!2) t = (Is!0) t  
                                                                       \<and> (Is!1) t + (Is!3) t = (Is!4) t  
                                                                       \<and> (Is!3) t + (Is!5) t = (Is!2) t
                                                                      \<and> (Is!4) t + (Is!5) t = (Is!0) t"
proof
  let ?I = "[Is!0, Is!1, Is!2, Is!3, Is!4, Is!5]"
  assume a1: "circuit_mat_imp (incidence_matrix \<N>s \<E>s) [Is!0, Is!1, Is!2, Is!3, Is!4, Is!5] t"
  have 1: "K *\<^sub>v (vecc ?I t) = 0\<^sub>v (dim_row K) " 
  using a1 by(simp add: circuit_mat_imp_def)
  then have a2: "\<And>i. i < dim_row K \<Longrightarrow> row K i \<bullet> (vecc ?I t) = 0"
  using index_mult_mat_vec index_zero_vec(1) 
  by metis
  then show "(Is!1) t + (Is!2) t = (Is!0) t "
  proof-
   have "(row K 0) \<bullet> (vecc ?I t) = 0"
      using 1 a2 m_non_zero by auto
    then have "row K 0 \<bullet> vec_of_list [(Is!0) t, (Is!1) t, (Is!2) t, (Is!3) t, (Is!4) t, (Is!5) t] = 0"
      by(simp add: curr_vec_open)
    then have "vec_of_list [-1::real, 1, 1, 0 , 0, 0] \<bullet> vec_of_list [(Is!0) t, (Is!1) t, (Is!2) t, (Is!3) t, (Is!4) t, (Is!5) t] = 0"
      using incidence_matrix_rlc Kinci_rowseq(1)
      by (simp add: assms)
    then have "(-1)*((Is!0) t) + 1*((Is!1) t)+ 1*((Is!2) t) + 0 * ((Is!3) t) + 0*((Is!4) t)+ 0* ((Is!5) t) = 0"
      using scalar_prod_def by (auto simp: field_simps)
    then have "-(Is!0) t + (Is!1) t + (Is!2) t = 0" by auto
    thus ?thesis by auto
  qed
  then show "(Is ! 1) t + (Is ! 3) t = (Is ! 4) t  \<and> (Is ! 3) t + (Is ! 5) t = (Is ! 2) t \<and> (Is ! 4) t + (Is ! 5) t = (Is ! 0) t"
  proof-
    have  "(Is ! 1) t + (Is ! 3) t = (Is ! 4) t"
    proof-
     have "(row K 1) \<bullet> (vecc ?I t) = 0"
        using 1 a1 a2 inci_matrow_dim m_non_zero 
        by (metis length_Cons list.size(3) assms(1) numeral_4_eq_4 one_less_numeral_iff semiring_norm(76))
      then have "vec_of_list [0::real, -1, 0, -1, 1, 0] \<bullet> vec_of_list [(Is!0) t, (Is!1) t, (Is!2) t, (Is!3) t, (Is!4) t, (Is!5) t] = 0"
        using incidence_matrix_rlc Kinci_rowseq(2) by(simp add: curr_vec_open assms)
      then have "(Is!1) t + (Is!3) t - (Is!4) t = 0"
        by auto
      thus ?thesis by auto
    qed
      moreover have "(Is ! 3) t + (Is ! 5) t = (Is ! 2) t "
      proof-
        have "(row K 2) \<bullet> (vecc ?I t) = 0"
          using a2 edge_open_unique_node_index assms m_non_zero nonempty_loop_system_axioms
          by (metis dim_row_K length_Cons less_Suc_eq list.size(3) numeral_2_eq_2)
         then have "vec_of_list  [0::real, 0, -1, 1, 0, 1] \<bullet> vec_of_list [(Is!0) t, (Is!1) t, (Is!2) t, (Is!3) t, (Is!4) t, (Is!5) t] = 0"
        using incidence_matrix_rlc Kinci_rowseq(3) by(simp add: curr_vec_open assms)
      thus ?thesis by auto
    qed
      moreover have "(Is ! 4) t + (Is ! 5) t = (Is ! 0) t"
      proof-
        have "(row K 3) \<bullet> (vecc ?I t) = 0"
        using a2 edge_open_unique_node_index assms m_non_zero
        by (metis inci_matrow_dim length_Cons less_Suc_eq list.size(3) numeral_3_eq_3)
      then have "vec_of_list [1::real, 0, 0, 0, -1, -1] \<bullet> vec_of_list [(Is!0) t, (Is!1) t, (Is!2) t, (Is!3) t, (Is!4) t, (Is!5) t] = 0"
        using incidence_matrix_rlc Kinci_rowseq(4) by(simp add: curr_vec_open assms)
      thus ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
qed

lemma KCL_inci_mat_eq: 
assumes "\<N>s = [n1::'a, n2, n3, n4]" "\<E>s = [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]"
shows "circuit_mat_imp (incidence_matrix \<N>s \<E>s) [Is!0, Is!1, Is!2, Is!3, Is!4, Is!5] t \<longleftrightarrow>
                                                                          (Is!1) t + (Is!2) t = (Is!0) t  
                                                                       \<and> (Is!1) t + (Is!3) t = (Is!4) t  
                                                                       \<and> (Is!3) t + (Is!5) t = (Is!2) t
                                                                      \<and> (Is!4) t + (Is!5) t = (Is!0) t" 
proof
   let ?I = "[Is!0, Is!1, Is!2, Is!3, Is!4, Is!5]"
   show "circuit_mat_imp K ?I t \<Longrightarrow>
    (Is ! 1) t + (Is ! 2) t = (Is ! 0) t \<and> (Is ! 1) t + (Is ! 3) t = (Is ! 4) t \<and> (Is ! 3) t + (Is ! 5) t = (Is ! 2) t \<and> (Is ! 4) t + (Is ! 5) t = (Is ! 0) t"
     using KCL_inci_mat_imp assms by auto
   show " (Is ! 1) t + (Is ! 2) t = (Is ! 0) t \<and> (Is ! 1) t + (Is ! 3) t = (Is ! 4) t \<and> (Is ! 3) t + (Is ! 5) t = (Is ! 2) t \<and> (Is ! 4) t + (Is ! 5) t = (Is ! 0) t \<Longrightarrow>
            circuit_mat_imp K ?I t"
   proof-
     assume a1: "(Is ! 1) t + (Is ! 2) t = (Is ! 0) t \<and> (Is ! 1) t + (Is ! 3) t = (Is ! 4) t \<and> (Is ! 3) t + (Is ! 5) t = (Is ! 2) t \<and> (Is ! 4) t + (Is ! 5) t = (Is ! 0) t "
     show " circuit_mat_imp K ?I t"
     proof-
       have 0:"row K 0 = vec_of_list [-1::real, 1, 1, 0 , 0, 0]"
         using Kinci_rowseq(1) assms by auto
       have 1: "(Is ! 1) t + (Is ! 2) t = (Is ! 0) t" using a1 by auto
       have "vec_of_list [-1::real, 1, 1, 0 , 0, 0] \<bullet> vec_of_list [(Is!0) t, (Is!1) t, (Is!2) t, (Is!3) t, (Is!4) t, (Is!5) t] = 0"
         using 1 by auto       
       then have c0:"(row K 0) \<bullet> vecc ?I t = 0"
        using 0 circuit_mat_imp_def by(auto simp add: curr_vec_open)
       then have "(K  *\<^sub>v vecc ?I t) $0 = 0\<^sub>v (dim_row K)$0"
        using index_mult_mat_vec 
        by (metis dim_row_K index_zero_vec(1) m_non_zero)
       have 2: "(Is ! 1) t + (Is ! 3) t = (Is ! 4) t" using a1 by auto
       then have "vec_of_list  [0::real, -1, 0, -1, 1, 0] \<bullet> vec_of_list [(Is!0) t, (Is!1) t, (Is!2) t, (Is!3) t, (Is!4) t, (Is!5) t] = 0"
         by auto
       then have c1:"(row K 1) \<bullet> vecc ?I t = 0"
        using 0 circuit_mat_imp_def Kinci_rowseq(2) assms by(auto simp add: curr_vec_open)
        then have "(K  *\<^sub>v vecc ?I t) $1 = 0\<^sub>v (dim_row K)$1"
        using index_mult_mat_vec dim_row_K index_zero_vec(1)
        by (metis One_nat_def Suc_lessI edges_valid_nodes_index1 less_Suc0 m_non_zero n_non_zero)
      have 3: "(Is ! 3) t + (Is ! 5) t = (Is ! 2) t" using a1 by auto
        then have "vec_of_list [0::real, 0, -1, 1, 0, 1] \<bullet> vec_of_list [(Is!0) t, (Is!1) t, (Is!2) t, (Is!3) t, (Is!4) t, (Is!5) t] = 0"
         by auto
       then have c2:"(row K 2) \<bullet> vecc ?I t = 0"
        using 0 circuit_mat_imp_def Kinci_rowseq(3) assms by(auto simp add: curr_vec_open)
         have 4: "(Is!4) t + (Is!5) t = (Is!0) t" using a1 by auto
        then have "vec_of_list [1::real, 0, 0, 0, -1, -1] \<bullet> vec_of_list [(Is!0) t, (Is!1) t, (Is!2) t, (Is!3) t, (Is!4) t, (Is!5) t] = 0"
         by auto
       then have c3:"(row K 3) \<bullet> vecc ?I t = 0"
         using 0 circuit_mat_imp_def Kinci_rowseq(4) assms by(auto simp add: curr_vec_open)
       have 5: "dim_row K = 4" using assms(1) distincts(1) dim_row_K by auto
      then have "\<And>i. i < dim_row K \<Longrightarrow> row K i \<bullet> vecc ?I t = 0"
        using  c0 c1 c2 c3 
        by (smt (z3) Suc_1 Suc_eq_plus1 less_2_cases_iff less_Suc_eq numeral_3_eq_3 numeral_4_eq_4 numeral_Bit0 numeral_Bit1)
      then have "\<And>i. i < dim_row K \<Longrightarrow>(K *\<^sub>v (vecc ?I t))$ i  = 0\<^sub>v (dim_row K)$ i"
        using index_mult_mat_vec by fastforce
      then have "(K *\<^sub>v (vecc ?I t)) =  0\<^sub>v (dim_row K)" by auto
      then show "circuit_mat_imp K ?I t" using circuit_mat_imp_def by auto
    qed
  qed
qed

theorem KCL_eq_inci_mat:
assumes "\<N>s = [n1::'a, n2, n3, n4]" "\<E>s = [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]"
shows "circuit_mat_imp (incidence_matrix \<N>s \<E>s) [Is!0, Is!1, Is!2, Is!3, Is!4, Is!5] t \<longleftrightarrow> KCL_imp [Is!0, Is!1, Is!2, Is!3, Is!4, Is!5] t"
proof
  let ?I = "[Is!0, Is!1, Is!2, Is!3, Is!4, Is!5]"
  show "circuit_mat_imp K ?I t \<Longrightarrow> KCL_imp ?I t"
  proof-
    assume a1: "circuit_mat_imp K ?I t"
    then show "KCL_imp ?I t"
    proof-
      have " (Is!1) t + (Is!2) t = (Is!0) t \<and> (Is!1) t + (Is!3) t = (Is!4) t \<and> (Is!3) t + (Is!5) t = (Is!2) t  \<and> (Is!4) t + (Is!5) t = (Is!0) t"
        using a1 KCL_inci_mat_imp assms by auto
      thus ?thesis using kcl_circ_eqs by auto
    qed
  qed 
  show " KCL_imp ?I t \<Longrightarrow> circuit_mat_imp K ?I t "
  proof-
    assume a2: "KCL_imp ?I t" then show "circuit_mat_imp K ?I t "
      using KCL_inci_mat_eq kcl_circ_eqs a2 assms by auto
  qed
qed

text\<open>KVL - Loop matrix\<close>

definition KVL_imp :: "(real \<Rightarrow> real) list \<Rightarrow> real \<Rightarrow> bool" where 
    "KVL_imp Vs t \<equiv> KVL [Vs!0, Vs!1, (Vs!4)] t \<and> 
                    KVL [Vs!3, (Vs!4), -(Vs!5)] t \<and> 
                    KVL [Vs!2, (Vs!3), -(Vs!1)] t"
                   
lemma kvl_circ_eqs: "KVL_imp Vs t \<longleftrightarrow> (Vs!0) t + (Vs!1) t = - (Vs!4) t  
                                      \<and> (Vs!3) t + (Vs!4) t = (Vs!5) t  
                                      \<and> (Vs!2) t + (Vs!3) t = (Vs!1) t"                                     
  unfolding KVL_imp_def KVL_def by auto

text\<open>Verification of Loop matrix of the RLC circuit\<close> 

lemma loop_matrix_rlc: 
assumes  "\<E>s = [(n4::'a,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]"
"\<L>s = [[(n4,n1),(n1,n2),(n2,n4)],[(n3,n4),(n4,n2),(n2,n3)],[(n1,n3),(n3,n2),(n2,n1)]]"
 shows "(loop_matrix \<L>s \<E>s :: real mat) = mat_of_rows_list 6 [[1::real, 1, 0, 0, 1, 0],
                                               [0::real, 0, 0, -1, -1, 1], 
                                               [0::real, -1, 1, 1, 0, 0]]"  (is "_ = ?rhs")
proof(rule eq_matI)
  show c1: "dim_row C = dim_row ?rhs" 
    using assms distinct dim_row_is_l by auto
  show c2: "dim_col C = dim_col ?rhs" 
 using assms distincts dim_col_C by auto
  show "\<And>i j. i <dim_row ?rhs \<Longrightarrow>
           j < dim_col ?rhs \<Longrightarrow> C $$ (i, j) = ?rhs $$ (i, j)"
  proof-
    have 1: "dim_row C = 3"  using dim_row_is_l assms(2) by auto
    have 2: "n1 \<noteq> n2 \<and> n1 \<noteq> n3 \<and> n1 \<noteq> n4 \<and> n2 \<noteq> n3 \<and> n2 \<noteq> n4 \<and> n3 \<noteq> n4"
      using network_wf distincts(2) assms(1)
      by (metis (no_types, lifting) fst_conv list.set_intros(1) set_subset_Cons snd_conv subset_code(1)) 
 have pos00: "in_pos_loop (\<E>s!0) (\<L>s!0)" 
  proof-
    have "(\<E>s!0) \<in> set (\<L>s!0)" using assms by auto
    thus ?thesis using in_pos_loop wellformed_2[of "(\<L>s!0)"] lloop_list 
      by (metis assms length_pos_if_in_set list.set_intros(1) loop_matrow_dim nth_Cons_0)
  qed
 have pos01: "in_pos_loop (\<E>s!1) (\<L>s!0)"   
  using assms in_pos_loop wellformed_1 loops_list_nempty lloop_list 
  by (metis One_nat_def diff_Suc_1 length_greater_0_conv list.set_intros(1)
     list.set_intros(2) loop_matrow_dim nth_Cons_0 nth_Cons_numeral numeral_One) 
  have pos04b: " (\<E>s!4) \<in> set (\<L>s!0)" using assms by auto
  then have pos04: "in_pos_loop (\<E>s!4) (\<L>s!0)" using assms in_pos_loop
    by (metis dim_row_is_l length_Cons less_Suc_eq list.size(3) lloop_list nth_mem numeral_3_eq_3 numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27))
  have pos15b: "(\<E>s!5)\<in> set (\<L>s!1)"  using assms by auto
  then have pos15: "in_pos_loop (\<E>s!5) (\<L>s!1)"using assms in_pos_loop
    by (metis (no_types, lifting) length_Cons less_Suc_eq list.size(3) lloop_list loop_matrow_dim nth_mem 
      numeral_3_eq_3 numeral_eq_Suc one_less_numeral_iff pred_numeral_simps(2) 
     pred_numeral_simps(3) semiring_norm(26) semiring_norm(27) semiring_norm(77))
  have pos22b: "(\<E>s!2) \<in> set (\<L>s!2)" using assms  by auto
   then have pos22: "in_pos_loop (\<E>s!2) (\<L>s!2)" using assms in_pos_loop lloop_list
     by (metis One_nat_def Suc_1 length_Cons less_Suc_eq list.size(3) not_in_loop_indexed wf_neg_loop)
   have pos23b: "(\<E>s!3)\<in> set (\<L>s!2)"  using assms by auto
  then have pos23: "in_pos_loop (\<E>s!3) (\<L>s!2)" using assms in_pos_loop lloop_list
    by (metis (mono_tags, opaque_lifting) One_nat_def Suc_1 length_Cons less_Suc_eq list.size(3) not_in_loop_indexed numeral_3_eq_3 wf_neg_loop)
  have neg13b:" (reverse (\<L>s!1)) = [(n3,n2),(n2,n4),(n4,n3)]" using assms by(simp add: reverse_def)
  then have r13: "(\<E>s!3) \<in> set (reverse (\<L>s!1))" using assms by auto   
  then have neg13: "in_neg_loop (\<E>s!3) (\<L>s!1)" 
  proof-
    have "(\<E>s!3) \<notin> set (\<L>s!1)" using assms loop_distinct distincts 2 by auto   
    thus ?thesis using r13 in_neg_loop[of "(\<E>s!3)" "(\<L>s!1)"] assms 
      by (metis One_nat_def Suc_eq_plus1 less_Suc_eq_0_disj list.size(4) not_in_loop_indexed numeral_3_eq_3 wf_pos_loop)
  qed
 have neg14b: "(\<E>s!4)\<in> set (reverse (\<L>s!1))" using assms by auto  
   then have neg14: "in_neg_loop (\<E>s!4) (\<L>s!1)" 
   proof-
  have "(\<E>s!4) \<notin> set (\<L>s!1)" using assms loop_distinct distincts 2 by auto
  thus ?thesis using assms wf_neg_loop_iff
      neg14b in_neg_loop[of "(\<E>s!4)" "(\<L>s!1)"] by auto     
  qed
  have neg21b: "(\<E>s!1)\<in> set (reverse (\<L>s!2))" using assms by auto
  then have neg21: "in_neg_loop (\<E>s!1) (\<L>s!2)" 
   proof-
  have "(\<E>s!1) \<notin> set (\<L>s!2)" using assms loop_distinct distincts 2 by auto
  thus ?thesis using neg21b assms wf_neg_loop_iff 
        in_neg_loop[of "(\<E>s!1)" "(\<L>s!2)"] by auto  
qed
 have no02b: "(\<E>s!2) \<notin> set (\<L>s!0) \<and> (\<E>s!2)\<notin> set (reverse (\<L>s!0))"
    using assms loop_distinct distincts 2 by auto
  then have no02:  "\<not>in_neg_loop (\<E>s!2) (\<L>s!0) \<and> \<not> in_pos_loop (\<E>s!2) (\<L>s!0)"
    using assms wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no03b: " (\<E>s!3) \<notin> set (\<L>s!0) \<and> (\<E>s!3)\<notin> set (reverse (\<L>s!0))"
    using assms loop_distinct distincts 2 by auto
  then have no03:  "\<not>in_neg_loop (\<E>s!3) (\<L>s!0) \<and> \<not> in_pos_loop (\<E>s!3) (\<L>s!0)"
    using assms  wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no05b: " (\<E>s!5) \<notin> set (\<L>s!0) \<and> (\<E>s!5)\<notin> set (reverse (\<L>s!0))"
    using assms loop_distinct distincts 2 by auto
  then have no05:  "\<not>in_neg_loop (\<E>s!5) (\<L>s!0) \<and> \<not> in_pos_loop (\<E>s!5) (\<L>s!0)"
    using assms wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no10b: " (\<E>s!0) \<notin> set (\<L>s!1) \<and> (\<E>s!0)\<notin> set (reverse (\<L>s!1))"
    using assms loop_distinct distincts 2 by auto
  then have no10: "\<not>in_neg_loop (\<E>s!0) (\<L>s!1) \<and> \<not> in_pos_loop (\<E>s!0) (\<L>s!1)"
    using assms wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no11b: " (\<E>s!1) \<notin> set (\<L>s!1) \<and> (\<E>s!1)\<notin> set (reverse (\<L>s!1))"
    using assms loop_distinct distincts 2  by auto
  then have no11: "\<not>in_neg_loop (\<E>s!1) (\<L>s!1) \<and> \<not> in_pos_loop (\<E>s!1) (\<L>s!1)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no12b: " (\<E>s!2) \<notin> set (\<L>s!1) \<and> (\<E>s!2)\<notin> set (reverse (\<L>s!1))"
    using assms loop_distinct distincts 2 by auto
  then have no12:  "\<not>in_neg_loop (\<E>s!2) (\<L>s!1) \<and> \<not> in_pos_loop (\<E>s!2) (\<L>s!1)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no20b: " (\<E>s!0) \<notin> set (\<L>s!2) \<and> (\<E>s!0)\<notin> set (reverse (\<L>s!2))"
    using assms loop_distinct distincts 2 by auto
  then have no20:  "\<not>in_neg_loop (\<E>s!0) (\<L>s!2) \<and> \<not> in_pos_loop (\<E>s!0) (\<L>s!2)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no24b: "(\<E>s!4) \<notin> set (\<L>s!2) \<and> (\<E>s!4) \<notin> set (reverse (\<L>s!2))"
    using assms loop_distinct distincts 2 by auto
  then have no24: "\<not>in_neg_loop (\<E>s!4) (\<L>s!2) \<and> \<not> in_pos_loop (\<E>s!4) (\<L>s!2)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
  have no25b: "(\<E>s!5) \<notin> set (\<L>s!2) \<and> (\<E>s!5) \<notin> set (reverse (\<L>s!2))"
    using assms loop_distinct distincts 2 by auto
  then have no25: "\<not>in_neg_loop (\<E>s!5) (\<L>s!2) \<and> \<not> in_pos_loop (\<E>s!5) (\<L>s!2)"
    using wf_loop_system wf_neg_loop wf_pos_loop by blast
  fix i j  assume i: "i<dim_row ?rhs" and j: "j < dim_col ?rhs "
  have "C$$ (0,0) = ?rhs $$ (0,0)"
    using i j pos00 inpos_loop_C_one_iff c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover  have "C$$ (0,1) = ?rhs $$ (0,1)"
    using i j pos01 inpos_loop_C_one_iff c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (0,2) = ?rhs $$ (0,2)"
    using i j no02 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (0,3) = ?rhs $$ (0,3)"
    using i j no03 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (0,4) = ?rhs $$ (0,4)"
    using i j pos04 inpos_loop_C_one_iff c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (0,5) = ?rhs $$ (0,5)"
    using i j no05 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (1,0) = ?rhs $$ (1,0)"
    using i j no10 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (1,1) = ?rhs $$ (1,1)"
    using i j no11 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (1,2) = ?rhs $$ (1,2)"
    using i j no12 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (1,3) = ?rhs $$ (1,3)"
  using i j neg13 inneg_loop_C_mone_iff c1 c2 
    by (simp add: mat_of_rows_list_def) 
  moreover have "C$$ (1,4) = ?rhs $$ (1,4)"
    using i j neg14 inneg_loop_C_mone_iff c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover  have "C$$ (1,5) = ?rhs $$ (1,5)"
    using i j pos15 inpos_loop_C_one_iff c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover  have "C$$ (2,0) = ?rhs $$ (2,0)"
    using i j no20 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (2,1) = ?rhs $$ (2,1)"
    using i j neg21 inneg_loop_C_mone_iff c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (2,2) = ?rhs $$ (2,2)"
    using i j pos22 inpos_loop_C_one_iff c1 c2 
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (2,3) = ?rhs $$ (2,3)"
    using i j pos23 inpos_loop_C_one_iff c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (2,4) = ?rhs $$ (2,4)"
    using i j no24 not_inloop_C_zero c1 c2  
    by (simp add: mat_of_rows_list_def)
  moreover have "C$$ (2,5) = ?rhs $$ (2,5)"
    using i j no25 not_inloop_C_zero c1 c2 
    by (simp add: mat_of_rows_list_def)
  ultimately show  "C$$ (i,j) = ?rhs $$ (i,j)"  
    using i j c1 c2 assms distincts loop_distinct
    by (smt (z3) "1" Suc_1 dim_col_C length_Cons lessI less_2_cases less_SucE list.size(3) 
          numeral_2_eq_2 numeral_3_eq_3 numeral_4_eq_4 numeral_5_eq_5) 
 qed
qed

lemma loop_rows_list : "i < length [[1::real, 1, 0, 0, 1, 0],[0::real, 0, 0, -1, -1, 1],[0::real, -1, 1, 1, 0, 0]]                                                
 \<Longrightarrow>  length ([[1::real, 1, 0, 0, 1, 0],[0::real, 0, 0, -1, -1, 1],  [0::real, -1, 1, 1, 0, 0]]!i) = 6"                                                                                            
 by (simp add: nth_Cons')

lemma lhs_C_loop: 
  assumes "i < length [[1::real, 1, 0, 0, 1, 0],[0::real, 0, 0, -1, -1, 1],[0::real, -1, 1, 1, 0, 0]] "
  shows "(row (mat_of_rows_list 6 [[1::real, 1, 0, 0, 1, 0],[0::real, 0, 0, -1, -1, 1],[0::real, -1, 1, 1, 0, 0]]) i) 
= vec_of_list ([[1::real, 1, 0, 0, 1, 0],[0::real, 0, 0, -1, -1, 1],[0::real, -1, 1, 1, 0, 0]] !i) "
 using assms loop_rows_list row_mat_of_rows_list by blast

lemma Cloop_rows:
  assumes  "\<E>s = [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]"
          "\<L>s = [[(n4,n1),(n1,n2),(n2,n4)],[(n3,n4),(n4,n2),(n2,n3)],[(n1,n3),(n3,n2),(n2,n1)]]"
  shows "(row C 0) = vec_of_list [1::real, 1, 0, 0, 1, 0]"
        "(row C 1) = vec_of_list [0::real, 0, 0, -1, -1, 1]"
        "(row C 2) = vec_of_list [0::real, -1, 1, 1, 0, 0]"
  using lhs_C_loop loop_matrix_rlc assms by auto

lemma KVL_loop_mat_eq: 
assumes  "\<E>s = [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]"
         "\<L>s = [[(n4,n1),(n1,n2),(n2,n4)],[(n3,n4),(n4,n2),(n2,n3)],[(n1,n3),(n3,n2),(n2,n1)]]"
 shows "circuit_mat_imp (loop_matrix \<L>s \<E>s) [Vs!0, Vs!1, Vs!2, Vs!3, Vs!4, Vs!5] t 
                                                             \<longleftrightarrow> (Vs!0) t + (Vs!1) t = - ((Vs!4) t)  
                                                                 \<and> (Vs!3) t + (Vs!4) t = (Vs!5) t  
                                                                 \<and> (Vs!2) t + (Vs!3) t = (Vs!1) t"
proof
  let ?V = "[Vs!0, Vs!1, Vs!2, Vs!3, Vs!4, Vs!5]"
  show "circuit_mat_imp (loop_matrix \<L>s \<E>s) ?V t \<Longrightarrow> (Vs!0) t + (Vs!1) t = - ((Vs!4) t)  
                                                     \<and> (Vs!3) t + (Vs!4) t = (Vs!5) t  
                                                     \<and> (Vs!2) t + (Vs!3) t = (Vs!1) t"
  proof
    assume a1 : "circuit_mat_imp C ?V t"
    have 0: "dim_row C = 3" 
      using assms distincts distinct dim_row_is_l by force 
    have 1: "C *\<^sub>v (vecc ?V t) = 0\<^sub>v (dim_row C) " 
      using a1 by(simp add: circuit_mat_imp_def)
    then have a2: "\<And>i. i < dim_row C \<Longrightarrow> (row C i)  \<bullet> (vecc ?V t) = 0"
      using index_mult_mat_vec index_zero_vec(1)  by metis
    then show "(Vs!0) t + (Vs!1) t = - ((Vs!4) t)"
    proof-
      have "row C 0 \<bullet> (vecc ?V t) = 0" 
        using 1 a2 by (simp add: loops_list_nempty)
      then have "vec_of_list [1::real, 1, 0, 0, 1, 0] \<bullet> vec_of_list [(Vs!0) t, (Vs!1) t, (Vs!2) t, (Vs!3) t, (Vs!4) t, (Vs!5) t] = 0 "
        using loop_matrix_rlc Cloop_rows(1) curr_vec_open by(simp add: assms)
      thus ?thesis by auto
    qed
    then show "(Vs ! 3) t + (Vs ! 4) t = (Vs ! 5) t \<and> (Vs ! 2) t + (Vs ! 3) t = (Vs ! 1) t"
    proof-
      have "(Vs ! 3) t + (Vs ! 4) t = (Vs ! 5) t "
      proof-
       have "row C 1 \<bullet> (vecc ?V t) = 0" 
         using a2 0 by auto
       thus ?thesis 
         using loop_matrix_rlc Cloop_rows(2) curr_vec_open by(simp add: assms)
     qed
     moreover have "(Vs ! 2) t + (Vs ! 3) t = (Vs ! 1) t"
     proof-
       have "row C 2 \<bullet> (vecc ?V t) = 0" 
          using a2 0 by auto
       thus ?thesis 
         using loop_matrix_rlc Cloop_rows(3) curr_vec_open by(simp add: assms)
     qed
     ultimately show ?thesis by auto
   qed
 qed
  show "(Vs!0) t + (Vs!1) t = - ((Vs!4) t) \<and> (Vs!3) t + (Vs!4) t = (Vs!5) t \<and> (Vs!2) t + (Vs!3) t = (Vs!1) t
        \<Longrightarrow> circuit_mat_imp (loop_matrix \<L>s \<E>s) ?V t"                                                         
  proof-
    assume b1: "(Vs!0) t + (Vs!1) t = - ((Vs!4) t) \<and> (Vs!3) t + (Vs!4) t = (Vs!5) t \<and> (Vs!2) t + (Vs!3) t = (Vs!1) t"
    show "circuit_mat_imp (loop_matrix \<L>s \<E>s) ?V t"
    proof-
      have 0 : "dim_row C = 3" using assms  dim_row_is_l by fastforce
      have b0: "row C 0 = vec_of_list [1::real, 1, 0, 0, 1, 0] "
        using  Cloop_rows(1) assms by auto
      have b2: "(Vs!0) t + (Vs!1) t = - ((Vs!4) t) " using b1 by auto
      then have  "vec_of_list [1::real, 1, 0, 0 , 1, 0] \<bullet> vec_of_list [(Vs!0) t, (Vs!1) t, (Vs!2) t, (Vs!3) t, (Vs!4) t, (Vs!5) t] = 0"
         using b2  by fastforce       
      have d0:"(row C 0) \<bullet> vecc ?V t = 0"
         using b0 b2 curr_vec_open by simp              
      have b3: "(Vs!3) t + (Vs!4) t = (Vs!5) t" using b1 by auto
      have b33: "row C 1 = vec_of_list [0::real, 0, 0, -1, -1, 1]"
        using  Cloop_rows(2) assms by auto
      then have "vec_of_list [0::real, 0, 0, -1, -1, 1] \<bullet> vec_of_list [(Vs!0) t, (Vs!1) t, (Vs!2) t, (Vs!3) t, (Vs!4) t, (Vs!5) t] = 0"
         using b3 curr_vec_open by fastforce    
      then have d1:"(row C 1) \<bullet> vecc ?V t = 0"
        using b33  by(auto simp add: curr_vec_open)       
       have 3: "(Vs!2) t + (Vs!3) t = (Vs!1) t" using b1 by auto
       then have "vec_of_list [0::real, -1, 1, 1, 0, 0] \<bullet>  vec_of_list [(Vs!0) t, (Vs!1) t, (Vs!2) t, (Vs!3) t, (Vs!4) t, (Vs!5) t] = 0"
         by auto
       then have d2:"(row C 2) \<bullet> vecc ?V t = 0"
        using 0 Cloop_rows(3) assms by(auto simp add: curr_vec_open)    
      then have "\<And>i. i < dim_row C \<Longrightarrow> row C i \<bullet> vecc ?V t = 0"
        using  d0 d1 d2 0 
        by (smt (z3) Suc_1 Suc_eq_plus1 less_2_cases_iff less_Suc_eq numeral_3_eq_3 numeral_4_eq_4 numeral_Bit0 numeral_Bit1)
      then have "\<And>i. i < dim_row C \<Longrightarrow>(C *\<^sub>v (vecc ?V t))$ i  = 0\<^sub>v (dim_row C)$ i"
        using index_mult_mat_vec by fastforce
      then have "(C *\<^sub>v (vecc ?V t)) =  0\<^sub>v (dim_row C)" by auto
      then show "circuit_mat_imp C ?V t" using circuit_mat_imp_def by auto
    qed
  qed
qed

theorem KVL_eq_loop_mat:
  assumes "\<E>s = [(n4,n1), (n1,n2), (n1,n3), (n3,n2), (n2,n4), (n3,n4)]" "\<L>s = [[(n4,n1),(n1,n2),(n2,n4)],[(n3,n4),(n4,n2),(n2,n3)],[(n1,n3),(n3,n2),(n2,n1)]]"
shows "circuit_mat_imp (loop_matrix \<L>s \<E>s) [Vs!0, Vs!1, Vs!2, Vs!3, Vs!4, Vs!5] t \<longleftrightarrow> KVL_imp [Vs!0, Vs!1, Vs!2, Vs!3, Vs!4, Vs!5] t"
  using assms KVL_loop_mat_eq kvl_circ_eqs by auto

end 
end