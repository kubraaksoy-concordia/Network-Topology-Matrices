theory Network_Cutset_System
  imports Network_Loop_System 
begin 

text \<open>Some auxiliary definitions and lemmas\<close>  
definition proper_sub_plist  :: "'a edges \<Rightarrow> 'a edges list" where
  "proper_sub_plist E \<equiv> [es <- (subseqs E). es \<noteq> []  \<and> es \<noteq> E \<and> distinct E]" 
                                                                                                                                                                                  
definition prop_subplist_on :: "'a edges \<Rightarrow> 'a edges \<Rightarrow> bool" where
  "prop_subplist_on es E \<equiv> es \<in> set (subseqs E) \<and> es \<noteq> []  \<and> es \<noteq> E \<and> distinct E" 
                         
lemma proper_subplist_alt: 
  fixes E :: "'a edges"     
  assumes "distinct E"
  shows "es \<in> set (proper_sub_plist E) \<Longrightarrow> es \<in> set (subseqs E) \<Longrightarrow> es \<noteq> [] \<Longrightarrow> es \<noteq> E "
  using assms
  by (simp add: proper_sub_plist_def)
       
definition proper_sub_list  :: "'a nodes \<Rightarrow> 'a nodes list" where
  "proper_sub_list V \<equiv> [vs <- (subseqs V). vs \<noteq> [] \<and> vs \<noteq> V \<and> distinct V]"

definition  proper_sublist_on where
"proper_sublist_on vs V \<equiv> vs \<in> set (subseqs V) \<and> vs \<noteq> [] \<and> vs \<noteq> V \<and> distinct V "

lemma proper_sublist_eq [simp] : "vs \<in> set (proper_sub_list V) \<longleftrightarrow> vs \<in> set (subseqs V) \<and>  vs \<noteq> []  \<and> vs \<noteq> V \<and> distinct V"
  unfolding proper_sub_list_def by auto

lemma prorper_sublistD : "vs \<in> set (proper_sub_list V) \<Longrightarrow> vs \<in> set (subseqs V) \<Longrightarrow>  vs \<noteq> [] \<and> vs \<noteq> V "
  unfolding proper_sub_list_def by auto

lemma proper_sublist_altdef: 
  assumes "distinct V"
  shows "\<And>vs. vs \<in> set (proper_sub_list V) \<longleftrightarrow> vs \<in> set (subseqs V) \<and> vs \<noteq> []  \<and> vs \<noteq> V"
  using assms 
  by (simp add: proper_sub_list_def)

lemma proper_sublist_alt: 
  assumes "distinct V"
  shows "vs \<in> set (subseqs V) \<Longrightarrow> vs \<noteq> [] \<Longrightarrow> vs \<noteq> V \<Longrightarrow> vs \<in> set (proper_sub_list V)"
  using assms by (simp add: proper_sub_list_def)

lemma ex: 
  assumes "distinct [a1, a2]"
  shows "proper_sub_list [a1, a2] = [[a1], [a2]]"                                                   
  unfolding proper_sub_list_def using assms by auto

abbreviation "diff_plist" :: "'a edges \<Rightarrow> 'a edges \<Rightarrow> 'a edges"  
  where "diff_plist es ps \<equiv> (if es = ps then [] else [x \<leftarrow> es. x \<notin> set ps])"

abbreviation "diff_list" :: "'a nodes \<Rightarrow> 'a nodes \<Rightarrow> 'a nodes"  
  where "diff_list es ps \<equiv> (if es = ps then [] else [x \<leftarrow> es. x \<notin> set ps])"

definition edges_to_nodes :: "'a edges\<Rightarrow> 'a nodes" where
"edges_to_nodes ps \<equiv> remdups (List.union (map fst ps) (map snd ps))"

(************************************************************************)        
context nonempty_network_system
begin

definition connected :: "'a nodes \<Rightarrow> 'a edges \<Rightarrow> bool" where
  "connected V E \<equiv>  nonempty_network_system V E \<and> (\<forall> v1 \<in> set V. \<forall>vx \<in> set V. (\<exists>ps. is_netw_gen_path v1 ps vx))"

lemma connectedI: "nonempty_network_system V E \<Longrightarrow> (\<forall> v1 \<in> set V. \<forall>vx \<in> set V. (\<exists>ps. is_netw_gen_path v1 ps vx)) \<Longrightarrow> connected V E"
  by (simp add: connected_def)

definition subgraph :: "'a nodes \<Rightarrow> 'a edges \<Rightarrow> bool" where
  "subgraph V E \<equiv> nonempty_network_system V E \<and> set V \<subseteq> set \<N>s \<and> set E \<subseteq> set \<E>s"
          
lemma subgraphI[simp] : "\<lbrakk>nonempty_network_system V E; set V \<subseteq> set \<N>s; set E \<subseteq> set \<E>s\<rbrakk> \<Longrightarrow> subgraph V E"
  using subgraph_def by auto

lemma subgraphE[simp] : " subgraph V E \<Longrightarrow> nonempty_network_system V E \<and> set V \<subseteq> set \<N>s \<and> set E \<subseteq> set \<E>s"
  using subgraph_def by auto

lemma subgraph_alt_network: "subgraph V E \<Longrightarrow> nonempty_network_system V E"
  by simp

lemma subgraph_alt_sub: "subgraph V E \<Longrightarrow> set V \<subseteq> set \<N>s \<and> set E \<subseteq> set \<E>s"
  by simp

definition proper_subgraph :: "'a nodes \<Rightarrow> 'a edges \<Rightarrow> bool" where
  "proper_subgraph V E \<equiv> subgraph V E \<and> (set V \<noteq> set \<N>s \<and> set E \<noteq> set \<E>s)"

lemma proper_subgraph_alt: 
  assumes "subgraph V E"
  shows "proper_subgraph V E \<longleftrightarrow> (set V \<noteq> set \<N>s \<and> set E \<noteq> set \<E>s)"
  using assms proper_subgraph_def by blast

lemma proper_subgraphE: "proper_subgraph V E \<Longrightarrow> subgraph V E \<Longrightarrow> set V \<noteq> set \<N>s \<Longrightarrow> set E \<noteq> set \<E>s"
  using proper_subgraph_def by blast

lemma propersub_is_sub: "proper_subgraph V E \<Longrightarrow> subgraph V E" 
  by (meson proper_subgraph_def)

text \<open>Let V1 be nonempty proper subset of node \<N>, and let V2 = \<N> - V1.
Then, a cut is defined as the set of edges and each of which is incident with one of its two endpoints in V1 and the other in V2 or vice-versa.\<close>
text\<open>Positive cut is a subset of edges that the first endpoint of elements is in V1 and the second is in V2\<close> 

definition pos_cut_list :: "'a nodes \<Rightarrow>  'a edges" where 
"pos_cut_list U \<equiv> [e <- \<E>s. fst e \<in> set U \<and> snd e \<in> set \<N>s - set U  \<and> U \<in> set (proper_sub_list \<N>s)]"

lemma pos_cut_filter: "pos_cut_list U = (filter (\<lambda> e . fst e \<in> set U \<and> snd e \<in> set \<N>s-set U \<and> U \<in> set (proper_sub_list \<N>s)) \<E>s)"
  using pos_cut_list_def by simp           
                                                              
lemma pos_cut_list_alt: 
  "e \<in> set (pos_cut_list U) \<longleftrightarrow> e \<in> set \<E>s \<and> fst e \<in> set U \<and> snd e \<in> set \<N>s-set U \<and> U \<in> set (proper_sub_list \<N>s)"
  unfolding pos_cut_list_def  by (simp add: wf_nonempty_netw_list_sys)      
                                                                                                                         
lemma pos_cut_listE: "e \<in> set (pos_cut_list U) \<Longrightarrow>  U \<in> set (proper_sub_list \<N>s) \<Longrightarrow> fst e \<in> set U \<and> snd e \<in> set \<N>s - set U  \<Longrightarrow> e \<in> set \<E>s"
 using wf_nonempty_netw_list_sys by(simp add: pos_cut_list_alt)                                                                                        
                                               
lemma pos_cut_listI:
  assumes " U \<in> set (proper_sub_list \<N>s)"  
  shows "fst e \<in> set U \<Longrightarrow> snd e \<in> set \<N>s - set U \<Longrightarrow> e \<in> set \<E>s \<Longrightarrow> e \<in> set (pos_cut_list U)"
  using assms  by(simp add: pos_cut_list_alt)  
                      
text\<open>Negative cut is a subset of edges and its first endpoint of elements is in V2 and the second is in V1\<close> 
     
definition neg_cut_list :: "'a nodes \<Rightarrow>  'a edges" where 
"neg_cut_list U \<equiv> [e <- \<E>s. snd e \<in> set U \<and> fst e \<in> set \<N>s - set U  \<and>  U \<in> set (proper_sub_list \<N>s)]"

lemma neg_cut_filter: "neg_cut_list U = (filter (\<lambda> e . snd e \<in> set U \<and> fst e \<in> set \<N>s - set U  \<and>  U \<in> set (proper_sub_list \<N>s)) \<E>s)"
  using neg_cut_list_def by simp

lemma neg_cut_list_alt:  "e \<in> set (neg_cut_list U) \<longleftrightarrow> e \<in> set \<E>s \<and> snd e \<in> set U \<and> fst e \<in> set \<N>s - set U  \<and>  U \<in> set (proper_sub_list \<N>s)"
  unfolding neg_cut_list_def by (simp add: wf_nonempty_netw_list_sys)                              
                                                                                                               
lemma neg_cut_listE: "e \<in> set (neg_cut_list U) \<Longrightarrow>  U \<in> set (proper_sub_list \<N>s) \<Longrightarrow>  snd e \<in> set U \<and> fst e \<in> set \<N>s-set U  \<Longrightarrow> e \<in> set \<E>s"
  by(simp add: neg_cut_list_def)                                               
            
lemma neg_cut_listI: assumes "U \<in> set (proper_sub_list \<N>s)"
  shows "snd e \<in> set U \<Longrightarrow>  fst e \<in> set \<N>s - set U \<Longrightarrow> e \<in> set \<E>s \<Longrightarrow> e \<in> set (neg_cut_list U)"
  using assms by(simp add: neg_cut_list_def wf_nonempty_netw_list_sys)
                                          
lemma pos_cut_not_neg: "e \<in> set (neg_cut_list U) \<Longrightarrow> e \<notin> set (pos_cut_list U)"
 by(simp add: neg_cut_list_def pos_cut_list_def)

lemma neg_cut_not_pos: "e \<in> set (pos_cut_list U) \<Longrightarrow> e \<notin> set (neg_cut_list U)"
 by(simp add: neg_cut_list_def pos_cut_list_def)
                                        
lemma invalid_cut_pos_neg:    
  shows "U \<notin> set (proper_sub_list \<N>s) \<Longrightarrow> e \<notin> set (pos_cut_list U) \<Longrightarrow> e \<notin> set (neg_cut_list U) "
  using neg_cut_list_alt by blast
             
lemma no_neg_cut_not_pos1: 
  shows "e \<notin> \<E> \<Longrightarrow> e \<notin> set (pos_cut_list U) \<and> e \<notin> set (neg_cut_list U)"
  using neg_cut_list_alt pos_cut_list_alt by blast          
                                      
text\<open>Cut is defined as union of positive and negative cut lists\<close>
                                   
definition cut_list :: "'a nodes \<Rightarrow>  'a edges" where 
"cut_list U \<equiv> List.union (pos_cut_list U) (neg_cut_list U)"
                                
lemma negcut_is_cut: "e \<in> set (neg_cut_list U) \<Longrightarrow> e \<in> set (cut_list U)"
  unfolding cut_list_def by(simp add: UnI1)

lemma poscut_is_cut: "e \<in> set (pos_cut_list U) \<Longrightarrow> e \<in> set (cut_list U)"
  unfolding cut_list_def by(simp add: UnI1)

lemma cut_list_pos_neg: "e \<in> set (cut_list U) \<Longrightarrow> e \<in>  set (neg_cut_list U) \<or> e \<in> set (pos_cut_list U)"
  unfolding cut_list_def by auto

lemma not_cut_list_pos_neg: "e \<notin> set (cut_list U) \<Longrightarrow> e \<notin> set (neg_cut_list U) \<and> e \<notin> set (pos_cut_list U)"
  unfolding cut_list_def by simp  

lemma invalid_cut: "U \<notin> set (proper_sub_list \<N>s) \<Longrightarrow> e \<notin> set (cut_list U)"
  using cut_list_pos_neg neg_cut_list_alt pos_cut_list_alt by blast               
                    
text \<open>
The set of edges in a connected graph G is called a cutset of G if removal of the set from G leaves G disconnected 
but no proper subsets of the cutset does not do so
-Cutset is a subgraph of connected graph G\<close>

definition cuts_sgraph :: "'a nodes \<Rightarrow> 'a edges \<Rightarrow> bool" where
"cuts_sgraph V E \<equiv> 
connected \<N>s \<E>s \<and> subgraph V E \<and> 
 \<not> connected \<N>s (diff_plist \<E>s E) \<and> 
(\<forall>K \<in> set (proper_sub_plist E). connected (edges_to_nodes K) K)"
   
lemma cut_sets_alt:  
  assumes "connected \<N>s \<E>s" and "subgraph V E"
  shows "cuts_sgraph V E \<longleftrightarrow> \<not> connected \<N>s (diff_plist \<E>s E) \<and> (\<forall>K \<in> set (proper_sub_plist E). connected (edges_to_nodes K) K)"
  using assms by (simp add: cuts_sgraph_def)

definition cutset_edges :: "'a nodes \<Rightarrow> 'a edges"  where
"cutset_edges U \<equiv> [e \<leftarrow> (cut_list U). connected \<N>s \<E>s \<and> subgraph (\<N>s) (cut_list U) \<and> \<not> (connected \<N>s (diff_plist \<E>s (cut_list U)))
                    \<and> (\<forall>K \<in> set (proper_sub_plist (cut_list U)). connected (edges_to_nodes K) K)]"

definition cutset :: "'a nodes \<Rightarrow> 'a edges"  where
"cutset U \<equiv> [e \<leftarrow> (cut_list U). cuts_sgraph \<N>s (cut_list U)]"

lemma cutset_edges: shows "cutset U = cutset_edges U"
  unfolding cutset_def cutset_edges_def using cuts_sgraph_def by presburger

lemma cutset_edges_iff: assumes "connected \<N>s \<E>s" 
  shows "e \<in> set (cutset_edges U) \<longleftrightarrow> e \<in> set (cut_list U) \<and> subgraph (\<N>s) (cut_list U) 
          \<and> \<not> (connected \<N>s (diff_plist \<E>s (cut_list U))) 
          \<and> (\<forall>K \<in> set (proper_sub_plist (cut_list U)). connected (edges_to_nodes K) K)"
  using assms  by(simp add: cutset_edges_def)
                                                        
lemma cutset_edgesE:  assumes "connected \<N>s \<E>s" 
  shows "e \<in> set (cutset_edges U) \<Longrightarrow> subgraph (\<N>s) (cut_list U) \<Longrightarrow> \<not> (connected \<N>s (diff_plist \<E>s (cut_list U))) \<Longrightarrow>  
        (\<forall>K \<in> set (proper_sub_plist (cut_list U)). connected (edges_to_nodes K) K) \<Longrightarrow> e \<in> set (cut_list U)"
  using assms by(simp add: cutset_edges_iff)
                          
lemma cutset_edgesI: assumes "connected \<N>s \<E>s" and "subgraph (\<N>s) (cut_list U)"
  shows " e \<in> set (cut_list U) \<Longrightarrow> \<not> (connected \<N>s (diff_plist \<E>s (cut_list U))) \<Longrightarrow> (\<forall>K \<in> set (proper_sub_plist (cut_list U)). connected (edges_to_nodes K) K)\<Longrightarrow> e \<in> set (cutset_edges U)"
  using assms by(simp add: cutset_edges_def)
                                        
abbreviation "N \<equiv> proper_sub_list \<N>s"  (*'a list list*)     
abbreviation "t \<equiv> length (proper_sub_list \<N>s)"

end

locale cutset_system = nonempty_network_system +
  fixes cutsets_list :: "'a edges list" ("\<C>s")
  assumes wf_1: "cs \<in> set \<C>s \<Longrightarrow> set cs \<subset> \<E>" and dist: "distinct \<C>s" 
  assumes wf_2: "U \<in> set N \<Longrightarrow> (cutset_edges U) \<in> set \<C>s" 
begin 

abbreviation "z \<equiv> length \<C>s"
abbreviation "\<C> \<equiv> set \<C>s"

lemma wf_cutset_system: "cutset_system \<N>s \<E>s \<C>s"  by intro_locales

lemma wf_cutset_in_edges: 
  assumes "cs \<in> \<C>" and "distinct \<C>s"
  shows "cutset_system \<N>s \<E>s \<C>s \<longrightarrow> set cs \<subset> \<E>"
  using wf_1 assms by auto

lemma wf_cuts_are_csets:
 assumes "cs \<in> \<C>" and "distinct \<C>s" and "U \<in> set N"
shows "cutset_system \<N>s \<E>s \<C>s \<longrightarrow> (cutset_edges U) \<in> set \<C>s"
  using wf_2 assms by auto

lemma wf_cutset_system_iff: 
  assumes "cs \<in> \<C>" and "distinct \<C>s" and "U \<in> set N"
  shows "cutset_system \<N>s \<E>s \<C>s \<longleftrightarrow>  set cs \<subset> \<E> \<and>  (cutset_edges U) \<in> set \<C>s"
   using wf_1 wf_2 assms by (auto simp add: wf_cutset_system)

lemma cutset_systemE: 
"U \<in> set N \<Longrightarrow> (cutset U) \<in> set \<C>s \<Longrightarrow> cs \<in> set \<C>s \<Longrightarrow> set cs \<subset> \<E> \<Longrightarrow> distinct \<C>s \<Longrightarrow> cutset_system \<N>s \<E>s \<C>s"
  using cutset_system_axioms by blast
                         
lemma wf_invalid_edge: "e \<notin> \<E> \<Longrightarrow> cs \<in> set \<C>s \<Longrightarrow> e \<notin> set cs"
  using wf_1 by auto

lemma wf_invalid_cs:
  shows  "cutset_edges U \<notin> set \<C>s \<Longrightarrow> U \<notin> set N" 
  using wf_2 by auto

lemma wf_nonemptycs_cs_exist:
  shows  "set \<C>s \<noteq> {} \<Longrightarrow> \<exists> cs U. cs = cutset U" 
  by auto

end

locale nonempty_cutset_system = cutset_system +
assumes cutsets_list_nempty: " \<C>s \<noteq> []"

begin 

lemma "cutset_system \<N>s \<E>s \<C>s \<Longrightarrow> nonempty_cutset_system \<N>s \<E>s \<C>s"
  by(simp add: nonempty_cutset_system_axioms)

lemma wf_cutset_nempty_alt: "\<forall>i \<in> {0..<length \<C>s}.  \<C>s!i \<notin> {}"
  by blast

lemma wf_edges_nempty_alt: "\<forall>i \<in> {0..<length \<C>s}. (\<forall>j \<in> {0..<length \<E>s}. \<C>s!i!j \<notin> {})"
  by blast

lemma cutset_indexing_inj: "\<forall> i \<in> H . i < length \<C>s \<Longrightarrow> inj_on ((!) \<C>s) H"
  using dist inj_on_nth by blast

lemma wf_cutsets_edge : "\<forall>i \<in> {0..<length \<C>s}.  set (\<C>s!i) \<subset> \<E>"
  using wf_1 by auto

lemma wf_cutsets_sub : "\<forall>t \<in> {0..<length N}. (cutset_edges (N!t)) \<in> \<C>"
  using wf_2 by (meson atLeastLessThan_iff nth_mem)

text \<open>Basic properties on loop_system \<close>

lemma cutset_list_length: "length \<C>s = z"
  by simp

lemma valid_edges_index_cons: 
  assumes "cs \<in>  \<C>" and "e \<in> \<E>"
  shows "e \<in> set cs \<Longrightarrow> \<exists> i. cs ! i = e \<and> i < length cs"
  by (meson in_set_conv_nth)
   
lemma valid_cutset_index: "i < z \<Longrightarrow> \<C>s ! i \<in> \<C>"
  using cutset_list_length by (metis nth_mem)

lemma valid_cutset_index_cons: "cs \<in> \<C> \<Longrightarrow> \<exists> i . \<C>s ! i = cs \<and> i < z"
  by (auto simp add: set_conv_nth)

lemma valid_cutset_index_index: "k < length (\<C>s!i) \<Longrightarrow>  \<C>s ! i ! k \<in> set (\<C>s!i)"
  by auto

lemma valid_cutset_elem_index_cons: "e \<in> set (\<C>s!i)  \<Longrightarrow> \<exists> k . \<C>s ! i ! k = e \<and> k < length (\<C>s!i) "
  by (meson in_set_conv_nth)

lemma valid_cutset_index_obtains: 
  assumes "cs \<in> \<C>"
  obtains i where  "\<C>s ! i = cs \<and> i < z"
  using assms valid_cutset_index_cons by auto

lemma cutset_set_image: "\<C> = image ( \<lambda> i.  (\<C>s!i)) ({0..<z})"
  by (metis list.set_map map_nth set_upt)

lemma cutset_set_list_image: 
  assumes "i < z" 
  shows "set (\<C>s!i)  = image ( \<lambda> k.  (\<C>s!i!k)) ({0..<length (\<C>s!i)})"
  using distincts by (metis list.set_map map_nth set_upt)

lemma cutset_betw_joints_index: "bij_betw (\<lambda> i. \<C>s ! i) {0..<z} \<C>"
proof (simp add: bij_betw_def, intro conjI)
  show "inj_on ((!) \<C>s) {0..<z}"
    by(simp add: cutset_indexing_inj)
  show "(!) \<C>s ` {0..<z} =  \<C>"
    using cutset_set_image by presburger
qed

text \<open>The cutset-edge relationship is given with a triple since every cutset is generated by the each elements of nonempty proper sub list\<close>

definition "C\<^sub>p \<equiv> {(u, e, cs). cs \<in> set \<C>s \<and> e \<in> set cs \<and>  e \<in> set (pos_cut_list u) \<and>  e \<in> set (cutset_edges u)}"   (*positively directed cutset*)

definition "C\<^sub>n \<equiv> {(u, e, cs). cs \<in> set \<C>s \<and> e \<in> set cs \<and> e \<in> set (neg_cut_list u) \<and> e \<in> set (cutset_edges u)}" (*negatively directed cutset*)
                                                                                                         
definition in_pos_cutset :: "'a nodes \<Rightarrow> 'a edge \<Rightarrow> 'a edges \<Rightarrow> bool"  
  where "in_pos_cutset u e cs \<equiv> (u, e, cs) \<in> C\<^sub>p"

definition in_neg_cutset :: "'a nodes \<Rightarrow>'a edge \<Rightarrow> 'a edges \<Rightarrow> bool" 
  where "in_neg_cutset u e cs \<equiv> (u, e, cs) \<in> C\<^sub>n"
         
lemma pos_cutset_altdef: "in_pos_cutset u e cs \<longleftrightarrow> e \<in> set \<E>s \<and> cs \<in> set \<C>s \<and> e \<in> set cs \<and> u \<in> set N \<and> e \<in> set (pos_cut_list u) \<and> e \<in> set (cutset_edges u)"
  using C\<^sub>p_def in_pos_cutset_def  pos_cut_list_alt by auto         

lemma in_pos_cutset: 
  assumes "cs \<in> set \<C>s"  "e \<in> set cs"
  shows "in_pos_cutset u e cs \<longleftrightarrow>  e \<in> set (pos_cut_list u) \<and> e \<in> set (cutset_edges u)"
  using assms pos_cut_list_alt pos_cutset_altdef by blast

lemma pos_cutsetI:  "cs \<in> set \<C>s \<Longrightarrow> e \<in> set cs \<Longrightarrow>  e \<in> set (pos_cut_list u) \<Longrightarrow>  e \<in> set (cutset_edges u) \<Longrightarrow> in_pos_cutset u e cs"
  using C\<^sub>p_def by (simp add: pos_cut_list_alt pos_cutset_altdef)   

 lemma pos_cutsetE:        
  shows "in_pos_cutset u e cs \<Longrightarrow> cs \<in> set \<C>s \<Longrightarrow> e \<in> set cs \<Longrightarrow>  e \<in> set (pos_cut_list u) \<Longrightarrow>  e \<in> set (cutset_edges u)"
   using in_pos_cutset_def pos_cutset_altdef by blast    
                                                   
lemma neg_cutset_altdef: "in_neg_cutset u e cs \<longleftrightarrow>  cs \<in> set \<C>s \<and> e \<in> set cs \<and> e \<in> set (neg_cut_list u) \<and> e \<in> set (cutset_edges u)"
      by (simp add:C\<^sub>n_def in_neg_cutset_def)

lemma in_neg_cutset:
  assumes "e \<in> set \<E>s" "cs \<in> set \<C>s" "e \<in> set cs"
  shows "in_neg_cutset u e cs \<longleftrightarrow>  e \<in> set (neg_cut_list u) \<and> e \<in> set (cutset_edges u)"
  using assms(2) assms(3) neg_cut_list_alt neg_cutset_altdef by blast

lemma neg_cutsetI: "e \<in> set \<E>s \<Longrightarrow> cs \<in> set \<C>s \<Longrightarrow>  e \<in> set cs \<Longrightarrow> u \<in> set N \<Longrightarrow> e \<in> set (neg_cut_list u) \<and> e \<in> set (cutset_edges u) \<Longrightarrow> in_neg_cutset u e cs"
    using C\<^sub>n_def wf_cutset_system in_neg_cutset_def by blast

lemma in_cutset_not_pos_but_neg: "\<not> in_pos_cutset u e cs \<and> in_neg_cutset u e cs \<Longrightarrow>  e \<in> set (neg_cut_list u)"
  using neg_cutset_altdef wf_cutset_system by blast
                                                                                      
lemma in_cutset_not_neg_but_pos: "\<not> in_neg_cutset u e cs \<and> in_pos_cutset u e cs \<Longrightarrow> e \<in> set (pos_cut_list u)"
  using pos_cutset_altdef wf_cutset_system by blast                                                              
                        
lemma not_pos_not_neg_notin_cutsets: "e \<notin> set (cutset_edges u) \<Longrightarrow> \<not> in_pos_cutset u e cs \<Longrightarrow> \<not>in_neg_cutset u e cs"
  using in_neg_cutset_def neg_cutset_altdef by blast   
                             
lemma notin_cutsets_not_pos_not_neg: "e \<notin> set cs \<Longrightarrow> \<not> in_pos_cutset u e cs \<and> \<not>in_neg_cutset u e cs"  
   by(simp add: neg_cutset_altdef pos_cutset_altdef)                                          

lemma neg_cutset_cond_indexed[simp]: "i < z \<Longrightarrow> j < n \<Longrightarrow> (\<E>s!j) \<in> set (\<C>s!i) 
 \<Longrightarrow> in_neg_cutset (N!i) (\<E>s!j) (\<C>s!i) \<Longrightarrow> (\<E>s!j) \<in> set (neg_cut_list (N!i))"
  using in_neg_cutset_def neg_cutset_altdef by blast     

lemma neg_cutset_cond_indexed_alt: "i < z \<Longrightarrow> j < n 
 \<Longrightarrow> in_neg_cutset (N!i) (\<E>s!j) (\<C>s!i) \<Longrightarrow> (\<E>s!j) \<in> set (\<C>s!i) \<and>  (\<E>s!j) \<notin> set (pos_cut_list (N!i))"
  using neg_cutset_cond_indexed neg_cutset_altdef pos_cut_not_neg by blast

lemma pos_cutset_cond_indexed[simp]: "i < z \<Longrightarrow> j < n \<Longrightarrow> (\<E>s!j) \<in> set (\<C>s!i) 
 \<Longrightarrow> in_pos_cutset (N!i) (\<E>s!j) (\<C>s!i) \<Longrightarrow> (\<E>s!j) \<in> set (pos_cut_list (N!i)) \<and> (\<E>s!j) \<notin> set (neg_cut_list (N!i))"          
  using pos_cut_not_neg by (metis pos_cutset_altdef)              

lemma pos_cutset_cond_indexed_alt: "i < z \<Longrightarrow> j < n 
 \<Longrightarrow> in_pos_cutset (N!i) (\<E>s!j) (\<C>s!i) \<Longrightarrow> (\<E>s!j) \<in> set (\<C>s!i) \<and> (\<E>s!j) \<in> set (pos_cut_list (N!i)) \<and> (\<E>s!j) \<notin> set (neg_cut_list (N!i))"
  using notin_cutsets_not_pos_not_neg pos_cutset_cond_indexed by blast

lemma in_cuts_neg_notpos_cutset_cond_indexed: "i < z \<Longrightarrow> j < n \<Longrightarrow> 
 in_neg_cutset (N!i) (\<E>s!j) (\<C>s!i) \<Longrightarrow> \<not> in_pos_cutset (N!i) (\<E>s!j) (\<C>s!i) \<longleftrightarrow>  (\<E>s!j) \<notin> set (pos_cut_list (N!i))"
  using neg_cutset_cond_indexed pos_cutset_cond_indexed pos_cut_not_neg 
  by (metis neg_cutset_cond_indexed_alt)                                                               

lemma in_cuts_pos_notneg_cutset_cond_indexed: "i < z \<Longrightarrow> j < n \<Longrightarrow> (\<E>s!j) \<in> set (\<C>s!i)              
 \<Longrightarrow> in_pos_cutset (N!i) (\<E>s!j) (\<C>s!i) \<Longrightarrow> \<not> in_neg_cutset (N!i) (\<E>s!j) (\<C>s!i) \<longleftrightarrow> (\<E>s!j) \<in> set (pos_cut_list (N!i)) \<and> (\<E>s!j) \<notin> set (neg_cut_list (N!i))"
  using neg_cutset_cond_indexed pos_cutset_cond_indexed pos_cutset_cond_indexed pos_cut_not_neg by blast                 
                                                                                                        
 lemma not_pos_nor_neg_ntin_cuts_cond_indexed: "i < z \<Longrightarrow> j < n \<Longrightarrow> (\<C>s!i) = (cutset (N!i)) 
\<Longrightarrow> \<not> (in_pos_cutset (N!i) (\<E>s!j) (\<C>s!i)) \<Longrightarrow> \<not> in_neg_cutset (N!i) (\<E>s!j) (\<C>s!i) \<Longrightarrow> (\<E>s!j) \<notin> set (\<C>s!i)"
 proof -
   assume a1: "\<C>s ! i = cutset (N ! i)"
   and a2: "i < z"
   and a3: "\<not> in_pos_cutset (N ! i) (\<E>s ! j) (\<C>s ! i)"
   and a4: "\<not> in_neg_cutset (N ! i) (\<E>s ! j) (\<C>s ! i)"
   have "\<C>s ! i \<in> \<C>"
     using a2 by force
   then have a5: "cutset (N ! i) \<in> \<C>"
     using a1 by simp
   have "cutset (N ! i) = cutset_edges (N ! i)"
     by (simp add: nonempty_network_system.cutset_edges wf_nonempty_netw_list_sys)
   then have "cutset_edges (N ! i) = \<C>s ! i"
     using a1 by auto
   then show ?thesis
     using a5 a4 a3 a1 
     by (smt (z3) cut_list_pos_neg cutset_def mem_Collect_eq neg_cutset_altdef pos_cutsetI nonempty_cutset_system_axioms set_filter)
 qed
                                                                                                                                                           
end
end