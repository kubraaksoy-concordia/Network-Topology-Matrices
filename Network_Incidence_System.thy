theory Network_Incidence_System
  imports Main 

begin 

type_synonym 'a edge = "('a \<times> 'a)"
type_synonym 'a edges = "('a \<times> 'a) list"
type_synonym 'a node = "'a" 
type_synonym 'a nodes = "'a list"

section \<open> Network System\<close>
text \<open>We consider a network represented by a directed graph with no self-loops
 and multi-edges\<close>

locale network_system =
 fixes nodes_list:: "'a nodes" ("\<N>s") and  edges_list:: "'a edges" ("\<E>s")
 assumes network_wf: "\<And>e. e \<in> set \<E>s \<Longrightarrow> fst e \<in> set \<N>s \<and> snd e \<in> set \<N>s \<and> fst e \<noteq> snd e"
    and  distincts: "distinct \<N>s" "distinct \<E>s"   
begin

abbreviation "m \<equiv> length \<N>s"
abbreviation "n \<equiv> length \<E>s"

abbreviation "\<N> \<equiv> set \<N>s"
abbreviation "\<E> \<equiv> set \<E>s"

definition pair_to_set :: "'a edge \<Rightarrow> 'a set" where
"pair_to_set e = {fst e, snd e}"

fun swapair :: "'a edge \<Rightarrow> 'a edge" where
"swapair e = (snd e, fst e)"

lemma wf_network_system: "network_system \<N>s \<E>s" by intro_locales

lemma wf_network_system_iff:
  "p \<in> \<E> \<Longrightarrow> network_system \<N>s \<E>s \<longleftrightarrow> (fst p \<in> \<N> \<and> snd p \<in> \<N> \<and> fst p \<noteq> snd p)"
proof -
  assume a1: "p \<in> \<E>"
  then have a2: "snd p \<in> \<N>"
    using network_wf by blast
  have a3: "fst p \<in> \<N>"
    using a1 network_wf by blast
 have "fst p \<noteq> snd p"
    using a1  by (simp add: network_wf)
  then show ?thesis
    using a2 a3 network_system_axioms by force 
qed

lemma distinct0: "x \<in> \<N> \<Longrightarrow> \<forall> y \<in> \<N> - {x}. x \<noteq> y"
  by auto

lemma distinct_node_index: "i < length \<N>s \<Longrightarrow> j < length \<N>s \<Longrightarrow> i \<noteq> j \<Longrightarrow> \<N>s!i \<noteq> \<N>s!j"
  using  distincts(1) by (simp add: distinct_conv_nth)

lemma distinct_edge_index: "i < length \<E>s \<Longrightarrow> j < length \<E>s \<Longrightarrow> i \<noteq> j \<Longrightarrow> \<E>s!i \<noteq> \<E>s!j"
  using  distincts(2) by (simp add: distinct_conv_nth)

lemma wf_invalid_nodes: "x \<notin> \<N> \<Longrightarrow> p \<in> \<E>  \<Longrightarrow> x \<noteq> fst p \<and> x \<noteq> snd p"
  using network_wf by blast

lemma no_self_loop: 
  shows "\<And>e. e \<in> \<E> \<Longrightarrow> fst e \<noteq> snd e"
  using network_wf by simp

lemma exists_nodes : 
  shows "e \<in> \<E> \<Longrightarrow> \<exists> x y. fst e = x \<and> snd e = y \<and> x \<noteq> y"
  using network_wf by auto

lemma edg_subs_nodes: "\<E> \<subseteq> \<N>\<times>\<N>"
  using mem_Times_iff network_wf by blast

lemma nodes_list_empty_iff: "\<N>s = [] \<longleftrightarrow> \<N>= {}"
   by auto

lemma edges_list_empty_iff: "\<E>s = [] \<longleftrightarrow> \<E> = {}"
  by auto

lemma node_emp: "\<N>s = [] \<longrightarrow> \<E>s = []"
  using edg_subs_nodes by auto

end

locale isolated_network = network_system +
  assumes iso: "length \<N>s = 1"
begin

lemma noedge: "length \<E>s = 0"
  using iso network_wf
  by (metis in_set_conv_nth length_0_conv length_greater_0_conv less_one)

lemma node_sing: "\<N>s = [x] \<longrightarrow>  \<E>s = []"
  by (metis list.simps(15) network_wf set_empty singletonD subset_empty subset_iff)

lemma node_sing_conv: "\<And>x. x \<in> \<N> \<and> (length \<N>s = 1) \<longrightarrow> (x,x) \<notin>  \<E>"
  using node_sing 
  by (metis fst_conv no_self_loop snd_conv)

end

locale finite_netw_sys = network_system + 
  assumes finite_nodes: "finite \<N>" and 
          finite_edges: "finite \<E>" 

locale noparallel_edgs_netw_sys = finite_netw_sys+
  assumes noparallel: "e \<in> \<E> \<Longrightarrow> (snd e, fst e) \<notin> \<E>"

locale nonempty_network_system =  finite_netw_sys +
assumes edges_nempty: " \<E>s \<noteq> []"
begin

lemma wf_nonempty_netw_list_sys: "nonempty_network_system \<N>s \<E>s"  by intro_locales

lemma wf_nodes_nempty_alt: "\<forall>i \<in> {0..<length \<N>s}.  \<N>s!i \<notin> {}"
  by blast

lemma wf_edges_nempty_alt: "\<forall>j \<in> {0..<length \<E>s}.  \<E>s!i \<notin> {}"
  by blast

lemma wf_n_non_zero_imp_m_non_zero: "n > 0 \<Longrightarrow> m > 0"
  using network_wf by fastforce

lemma n_non_zero: "n > 0"
  using  wf_edges_nempty_alt edges_nempty by auto

lemma m_non_zero: "m > 0"
  using wf_nodes_nempty_alt n_non_zero wf_n_non_zero_imp_m_non_zero by blast

lemma network_nodes_nempty: "\<N> \<noteq> {}"
  using m_non_zero by auto

lemma nodes_list_length: "length \<N>s = m"
  by auto

lemma edges_list_length: "length \<E>s = n"
  by auto

lemma nodes_indexing_inj: "\<forall> i \<in> F . i < length \<N>s \<Longrightarrow> inj_on ((!) \<N>s) F"
  by (simp add: distincts inj_on_nth)

lemma edges_indexing_inj: "\<forall> i \<in> F . i < length \<E>s \<Longrightarrow> inj_on ((!) \<E>s) F"
  by (simp add: distincts inj_on_nth)

lemma elen_non_zero: "length \<E>s \<ge> 1"
  using edges_nempty 
  by (simp add: Suc_leI)

lemma valid_nodes_index: "i < m \<Longrightarrow> \<N>s ! i \<in> \<N>"
 by auto

lemma valid_nodes_index_cons: "x \<in> \<N> \<Longrightarrow> \<exists> i. \<N>s ! i = x \<and> i < m"
  by (auto simp add: in_set_conv_nth)

lemma valid_nodes_index_obtains: 
  assumes "x \<in> \<N>"
  obtains i where "\<N>s ! i = x \<and> i < m"
  using valid_nodes_index_cons assms by auto

lemma index_eq_nodes:
  "\<lbrakk> i < length \<N>s; j < length \<N>s \<rbrakk> \<Longrightarrow> (\<N>s!i = \<N>s!j) = (i = j)"
  using distincts(1) by(auto simp: distinct_conv_nth)

lemma index_eq_edges:
  "\<lbrakk> i < length \<E>s; j < length \<E>s\<rbrakk> \<Longrightarrow> (\<E>s!i = \<E>s!j) = (i = j)"
  using distincts(2) by(auto simp: distinct_conv_nth)

lemma valid_edges_index: "j < n \<Longrightarrow> \<E>s ! j \<in> \<E> "
  by simp

lemma valid_edges_index_cons: "p \<in> \<E>  \<Longrightarrow> \<exists> j . \<E>s ! j = p \<and> j < n"
  by (auto simp add: in_set_conv_nth)

lemma valid_edges_index_obtains: 
  assumes "p \<in> \<E> "
  obtains j where  "\<E>s ! j = p \<and> j < n"
  using assms valid_edges_index_cons by blast

lemma edges_outdeg_index: 
  assumes "p \<in> \<E>" "x = fst p"
  obtains i where "i < length \<N>s \<and> \<N>s ! i = x"
  using  valid_edges_index_obtains assms
  by (metis valid_nodes_index_obtains wf_invalid_nodes)

lemma edges_indeg_index: 
  assumes "p \<in> \<E>" "y = snd p"
  obtains i where "i < length \<N>s \<and> \<N>s ! i = y"
  using  valid_edges_index_obtains assms
  by (metis valid_nodes_index_obtains wf_invalid_nodes)

lemma edges_valid_nodes_index: 
  assumes "p \<in> \<E>" 
  obtains i j where "i < length \<N>s \<and> j < length \<N>s \<and> i \<noteq> j \<and> \<N>s ! i = fst p \<and> \<N>s ! j = snd p"
  using  valid_edges_index_obtains assms distincts
  by (metis in_set_conv_nth network_wf)

lemma edges_valid_nodes_index1:
  assumes "j < n" 
  obtains i1 i2 where "i1 < length \<N>s \<and> i2 < length \<N>s \<and> i1 \<noteq> i2 \<and>  \<E>s!j = (\<N>s!i1, \<N>s!i2)"
  using assms distincts 
  by (metis edges_valid_nodes_index fst_eqD valid_edges_index prod.exhaust snd_eqD)

lemma nodes_list_index_img: "\<N> = image(\<lambda> i . (\<N>s ! i)) ({..<m})"
  using valid_nodes_index_cons valid_nodes_index by auto

lemma edges_list_index_img: "\<E> = image(\<lambda> i . (\<E>s ! i)) ({..<n})"
  using valid_edges_index_cons valid_edges_index by blast

lemma edge_open_unique_node_index:
  shows "i1 < m \<Longrightarrow> i2 < m \<Longrightarrow> j < n \<Longrightarrow> \<E>s!j = (\<N>s!i1, \<N>s!i2) \<Longrightarrow> i1\<noteq>i2"
  using  edges_valid_nodes_index1 network_wf index_eq_nodes by force

lemma edge_uniqueness:
 "e \<in> set \<E>s \<Longrightarrow>  (\<exists>!i1. \<exists>!i2.  i1 < m  \<and> i2 < m \<and> (i1 \<noteq> i2) \<and> e = (\<N>s!i1, \<N>s!i2))"
  using distincts network_wf edges_valid_nodes_index1
  by (smt (verit) fst_conv in_set_conv_nth network_system.distinct_node_index snd_eqD wf_network_system) 

lemma edges_index_bij_betw: "bij_betw (\<lambda> i . \<E>s ! i) {0..<length \<E>s} (set \<E>s)"
  using  bij_betw_def 
  by (simp add: atLeast0LessThan bij_betw_nth distincts(2))

text \<open>Positive and negative incident relation\<close>

definition I\<^sub>P :: "('a \<times> 'a \<times> 'a) set" where
"I\<^sub>P \<equiv> {(v,e). e \<in> set \<E>s \<and> fst e = v} " (*edge is directed away from node-positive*)

definition I\<^sub>N :: "('a \<times> 'a \<times> 'a) set" where 
"I\<^sub>N \<equiv> {(v,e). e \<in> set \<E>s \<and> snd e = v} " (*edge is directed toward node-negative*)

definition "pos_incident v e \<equiv> (v,e) \<in> I\<^sub>P"

definition "neg_incident v e \<equiv> (v,e) \<in> I\<^sub>N"

lemma pos_incident_netw_altdef: 
  assumes "e \<in> set \<E>s"
  shows "pos_incident x e \<longleftrightarrow> fst e = x"
  using pos_incident_def I\<^sub>P_def assms no_self_loop network_wf by auto

lemma  neg_incident_netw_altdef: 
  assumes "e \<in> set \<E>s"
  shows "neg_incident x e \<longleftrightarrow> snd e = x"
  using neg_incident_def I\<^sub>N_def assms no_self_loop by auto

lemma not_pos_not_neg_incident_netw: 
  assumes "e \<in> set \<E>s"
  shows "\<not> pos_incident x e \<and> \<not> neg_incident x e \<longleftrightarrow> snd e \<noteq> x \<and> fst e \<noteq> x"
  using neg_incident_netw_altdef pos_incident_netw_altdef  assms no_self_loop  by auto

lemma neg_incident_cond_indexed[simp]: "i < m \<Longrightarrow> j < n \<Longrightarrow> neg_incident (\<N>s ! i) (\<E>s ! j) \<longleftrightarrow> (\<N>s ! i) =  snd (\<E>s ! j)  "
  using neg_incident_netw_altdef valid_nodes_index valid_edges_index  network_wf by auto

lemma pos_incident_cond_indexed[simp]: "i < m \<Longrightarrow> j < n \<Longrightarrow>  pos_incident (\<N>s ! i) (\<E>s ! j) \<longleftrightarrow> (\<N>s ! i) = fst (\<E>s ! j)"
  using pos_incident_netw_altdef valid_nodes_index valid_edges_index network_wf by auto

lemma pos_not_neg_incident: "i < m \<Longrightarrow> j < n \<Longrightarrow> pos_incident (\<N>s ! i) (\<E>s ! j) \<Longrightarrow> \<not> neg_incident (\<N>s ! i) (\<E>s ! j) \<longleftrightarrow> (\<N>s ! i) = fst (\<E>s ! j)"
  by (metis neg_incident_netw_altdef no_self_loop nth_mem pos_incident_netw_altdef)

lemma neg_not_pos_incident: "i < m \<Longrightarrow> j < n \<Longrightarrow> neg_incident (\<N>s ! i) (\<E>s ! j) \<Longrightarrow> \<not> pos_incident (\<N>s ! i) (\<E>s ! j) \<longleftrightarrow> (\<N>s ! i) = snd (\<E>s ! j)"
  by (metis neg_incident_netw_altdef no_self_loop nth_mem pos_incident_netw_altdef)

lemma not_pos_not_neg_incident: "i < m \<Longrightarrow> j < n \<Longrightarrow> \<not> pos_incident (\<N>s ! i) (\<E>s ! j) \<and> \<not> neg_incident (\<N>s ! i) (\<E>s ! j) \<longleftrightarrow> (\<N>s ! i) \<noteq> snd (\<E>s ! j) \<and> (\<N>s ! i) \<noteq> fst (\<E>s ! j)"
  by auto

lemma bij_betw_nodes_index: "bij_betw (\<lambda> i. \<N>s ! i) {0..<m} \<N>"
proof(simp add: bij_betw_def, intro conjI)
  show "inj_on ((!) \<N>s) {0..<m}"
    by (simp add: nodes_indexing_inj)
  show "(!) \<N>s ` {0..<m} = \<N> "
  proof(intro subset_antisym subsetI)
    fix x assume " x \<in> (!) \<N>s ` {0..<m}"
    then obtain i where "x = \<N>s ! i" and "i<m" by auto
    then show "x \<in> \<N>"
      by(simp add: valid_nodes_index)
  next
    fix x assume "x \<in> \<N>"
    then obtain i where "\<N>s ! i = x" and "i<m" 
      using valid_nodes_index_cons by auto
    then show "x \<in> (!) \<N>s ` {0..<m}" by auto
  qed
qed

lemma fst_pos_elem: "(fst x, x) \<in> I\<^sub>P \<Longrightarrow> fst x \<in> fst ` (\<Union>x\<in>\<E>. {(fst x, x)})"
  using I\<^sub>P_def fst_conv image_iff by fastforce 

lemma snd_neg_elem: "(snd x, x) \<in> I\<^sub>N \<Longrightarrow> snd x \<in> fst ` (\<Union>x\<in>\<E>. {(snd x, x)})"
   using I\<^sub>N_def UN_I fst_conv image_eqI 
   by (smt (verit, best) case_prod_conv insert_iff mem_Collect_eq)

lemma pos_fst_exist: "\<forall>e\<in>\<E>. \<exists>v\<in>\<N>. fst e = v" 
  using network_wf by blast

lemma neg_snd_exist: "\<forall>e\<in>\<E>. \<exists>v \<in>\<N>. snd e = v" 
  using network_wf by blast

lemma bound_card_Ip:
assumes "card \<N> = m" "card \<E>= n"
shows "card I\<^sub>P \<le> m*n"
proof-
  have "I\<^sub>P  \<subseteq> \<N> \<times> \<E>"
    using I\<^sub>P_def network_wf
    by auto
  then have "card I\<^sub>P \<le>card  \<N> * card \<E>"
    using finite_nodes finite_edges card_mono 
    by (metis card_cartesian_product finite_SigmaI)
  thus ?thesis using assms by simp
qed

lemma bound_card_In:
assumes "card \<N> = m" "card \<E>= n"
shows "card I\<^sub>N \<le> m*n"
proof-
  have "I\<^sub>N  \<subseteq> \<N> \<times> \<E>"
    using I\<^sub>N_def network_wf
    by auto
  then have "card I\<^sub>N \<le>card  \<N> * card \<E>"
    using finite_nodes finite_edges card_mono 
    by (metis card_cartesian_product finite_SigmaI)
  thus ?thesis using assms by simp
qed

lemma case_1: assumes "i < length \<N>s" and "j < length \<E>s " 
  shows "fst (\<E>s!j) = \<N>s!i \<Longrightarrow> snd (\<E>s!j) \<noteq> \<N>s!i"
  using network_wf assms
  by (metis valid_edges_index)

lemma case_2: assumes "i < length \<N>s" and "j < length \<E>s " 
  shows "snd (\<E>s!j) = \<N>s!i \<Longrightarrow> fst (\<E>s!j) \<noteq> \<N>s!i"
  using case_1 assms by blast

lemma case_3: assumes "i < length \<N>s" and "j < length \<E>s " 
  shows "\<not> (snd (\<E>s!j) = \<N>s!i \<and> fst (\<E>s!j) = \<N>s!i)"
    using assms case_1 by blast

text\<open>In degree (neginc) and out degree (posinc)\<close>

definition posinc_num :: "'a \<Rightarrow> nat"  where
"posinc_num x \<equiv> card {(\<E>s!j)| j.  j < length \<E>s \<and> fst (\<E>s!j) = x}"

definition neginc_num :: "'a \<Rightarrow> nat"  where
"neginc_num x \<equiv> card {(\<E>s!j)| j.  j < length \<E>s \<and> snd (\<E>s!j) = x}"

definition posincs :: "'a \<Rightarrow> ('a \<times> 'a) set"  where
"posincs x \<equiv>  {(\<E>s!j)| j.  j < length \<E>s \<and> fst (\<E>s!j) = x}"

definition negincs :: "'a \<Rightarrow> ('a \<times> 'a) set"  where
"negincs x \<equiv> {(\<E>s!j)| j.  j < length \<E>s \<and> snd (\<E>s!j) = x}"

definition didegree  :: "'a \<Rightarrow> nat"
  where "didegree x = posinc_num x + neginc_num x"

lemma posinc_num_g0_exists: 
  assumes "posinc_num x > 0" 
  obtains e where "e \<in> \<E>" and "fst e = x"
  using assms posinc_num_def
  by (smt (verit, ccfv_threshold) Collect_cong Collect_mem_eq card.empty empty_set
            length_pos_if_in_set less_nat_zero_code list.size(3) valid_edges_index)

lemma neginc_num_g0_exists:
  assumes "neginc_num v > 0" 
  obtains e where "e \<in> \<E>" and "snd e = v"
  using assms neginc_num_def 
  by (smt (verit, ccfv_SIG) Collect_cong Collect_mem_eq card.empty empty_set 
     length_greater_0_conv length_pos_if_in_set list.size(3) valid_edges_index)

lemma mat_posoutdeg_inter:"\<forall>i\<in>{0..<m}. \<forall>k\<in>{0..<m}. i\<noteq>k \<longrightarrow> posincs (\<N>s!i) \<inter> posincs (\<N>s!k) = {}"
  unfolding posincs_def using index_eq_nodes by fastforce

lemma mat_negindeg_inter:"\<forall>i\<in>{0..<m}. \<forall>k\<in>{0..<m}. i\<noteq>k \<longrightarrow> negincs (\<N>s!i) \<inter> negincs (\<N>s!k) = {}"
   unfolding negincs_def using index_eq_nodes by fastforce

lemma mat_outdeg_union:"(\<Union>x\<in>\<N>. posincs x) = {(\<E>s!j)| j. j < length \<E>s}"
unfolding posincs_def 
proof
  show "(\<Union>x\<in>\<N>. {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = x}) \<subseteq> {\<E>s ! j |j. j < n}"
  proof
    fix e assume iik: "e \<in> (\<Union>x\<in>\<N>. {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = x})"
    then show "e \<in> {\<E>s ! j |j. j < n}"
    proof
      fix y assume ii: " y \<in> \<N> " "e \<in> {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = y}"
      then have "fst e = y" using ii by auto
      then have "e \<in> {\<E>s ! j |j. j < n}" 
        using ii(2) by blast
      thus ?thesis by auto
    qed
  qed
  show "{\<E>s ! j |j. j < n} \<subseteq> (\<Union>x\<in>\<N>. {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = x}) "
  proof
    fix e assume jjk: "e \<in> {\<E>s ! j |j. j < n}"
    then show "e \<in> (\<Union>x\<in>\<N>. {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = x})"
    proof
      obtain j where jj: "e = \<E>s ! j \<and> j < n" 
        using jjk by blast
      obtain y where "y \<in> \<N>" "e \<in> {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = y}"
        using jj  nth_mem pos_fst_exist by auto
      thus ?thesis by auto
    qed
  qed
qed

lemma mat_outdeg_cardn:"card (\<Union>x\<in>\<N>. posincs x) = length \<E>s"
  using mat_outdeg_union 
  by (metis (mono_tags, lifting) distinct_card distincts(2) set_conv_nth)

lemma mat_outdeg_alter:"(\<Union>x\<in>\<N>. posincs x) = (\<Union>i\<in>{0..<m}. (posincs (\<N>s!i)))"
  unfolding posincs_def
proof
  show "(\<Union>x\<in>\<N>. {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = x}) \<subseteq> (\<Union>i\<in>{0..<m}. {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = \<N>s ! i})"
  proof
    fix x assume xx: "x \<in> (\<Union>x\<in>\<N>. {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = x})"
    show "x \<in> (\<Union>i\<in>{0..<m}. {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = \<N>s ! i})"
      using xx 
      by (smt (verit, best) UN_iff atLeast0LessThan edges_outdeg_index lessThan_iff mem_Collect_eq nth_mem)
  qed
    show "(\<Union>i\<in>{0..<m}. {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = \<N>s ! i}) \<subseteq> (\<Union>x\<in>\<N>. {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = x})"
    proof
     fix x assume xx: " x \<in> (\<Union>i\<in>{0..<m}. {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = \<N>s ! i}) "
     show " x \<in> (\<Union>x\<in>\<N>. {\<E>s ! j |j. j < n \<and> fst (\<E>s ! j) = x}) "
       using xx by auto
   qed
 qed

lemma card_posout_index_alt: "(\<Sum>x\<in>\<N>. (posinc_num x)) =  (\<Sum>i\<in>{0..<m}. (posinc_num (\<N>s!i)))"  
  by (smt (verit, ccfv_threshold) bij_betw_nodes_index sum.cong sum.reindex_bij_betw)

lemma nodes_set_index: "\<N> = {\<N>s!i| i. i \<in> {0..<m}}"
  using distincts(1) valid_nodes_index_cons by fastforce

lemma edges_set_index: "\<E> = {\<E>s!j| j. j \<in> {0..<n}}"
  using distincts(2) valid_edges_index_cons 
  by (smt (verit) Collect_cong bij_betw_iff_bijections edges_index_bij_betw mem_Collect_eq set_conv_nth)

lemma mat_outdeg_eq_sumdeg:"card (\<Union>x\<in>\<N>. posincs x) = (\<Sum>x\<in>\<N>. posinc_num x)"
proof-
  define I where "I = {0..<m}"
  then have 1: "finite I" by simp
  have "finite \<N>" by(simp add: finite_nodes)
  then have 2:"\<forall>i\<in>I. finite (posincs (\<N>s!i))" 
    unfolding posincs_def using I_def by simp
  then have 3: "\<forall>i\<in>I.\<forall>k\<in>I. i\<noteq>k \<longrightarrow> posincs (\<N>s!i) \<inter> posincs (\<N>s!k) = {}"
    using mat_posoutdeg_inter I_def by simp
  have 4:  "card (\<Union>x\<in>\<N>. posincs x) = card (\<Union>((posincs) `({\<N>s!i| i. i \<in> I})))"
    using I_def nodes_set_index posincs_def by auto
  also have "... = (\<Sum>x\<in>{\<N>s!i| i. i \<in> I}. posinc_num x)"
    unfolding posincs_def posinc_num_def using 3 2 1 card_UN_disjoint
    by (smt (verit) Collect_cong I_def finite_nodes mem_Collect_eq nodes_set_index posincs_def sum.cong)
  thus ?thesis using 4 I_def nodes_set_index by force
qed

lemma mat_outdeg_eq_sumdeg_index:"card (\<Union>x\<in>\<N>. posincs x) = (\<Sum>i\<in>{0..<m}. (posinc_num (\<N>s!i)))" 
  using card_posout_index_alt mat_outdeg_eq_sumdeg by auto

lemma mat_outdeg_eq_sumdeg_index_n: "(\<Sum>i\<in>{0..<m}. (posinc_num (\<N>s!i))) = n"
  using mat_outdeg_cardn mat_outdeg_eq_sumdeg_index by auto

lemma mat_indeg_union:"(\<Union>x\<in>\<N>. negincs x) = {(\<E>s!j)| j. j < length \<E>s}"
unfolding negincs_def 
proof
  show "(\<Union>x\<in>\<N>. {\<E>s ! j |j. j < n \<and> snd (\<E>s ! j) = x}) \<subseteq> {\<E>s ! j |j. j < n}"
  proof
    fix e assume iik: "e \<in> (\<Union>x\<in>\<N>. {\<E>s ! j |j. j < n \<and> snd (\<E>s ! j) = x})"
    then show "e \<in> {\<E>s ! j |j. j < n}"
    proof
      fix y assume ii: " y \<in> \<N> " "e \<in> {\<E>s ! j |j. j < n \<and> snd (\<E>s ! j) = y}"
      then have "snd e = y" using ii by auto
      then have "e \<in> {\<E>s ! j |j. j < n}" 
        using ii(2) by blast
      thus ?thesis by auto
    qed
  qed
  show "{\<E>s ! j |j. j < n} \<subseteq> (\<Union>x\<in>\<N>. {\<E>s ! j |j. j < n \<and> snd (\<E>s ! j) = x}) "
  proof
    fix e assume jjk: "e \<in> {\<E>s ! j |j. j < n}"
    then show "e \<in> (\<Union>x\<in>\<N>. {\<E>s ! j |j. j < n \<and> snd (\<E>s ! j) = x})"
    proof
      obtain j where jj: "e = \<E>s ! j \<and> j < n" 
        using jjk by blast
      obtain y where "y \<in>  \<N>" "e \<in> {\<E>s ! j |j. j < n \<and> snd (\<E>s ! j) = y}"
        using jj  nth_mem neg_snd_exist by auto
      thus ?thesis by auto
    qed
  qed
qed

lemma mat_indeg_cardn:"card (\<Union>x\<in>\<N>. negincs x) = n"
  using negincs_def mat_indeg_union mat_outdeg_cardn 
  by (simp add: mat_outdeg_union)

lemma mat_indeg_alter:"(\<Union>x\<in>\<N>. negincs x) = (\<Union>i\<in>{0..<m}. ((negincs (\<N>s!i))))"
proof
  show "\<Union> (negincs ` \<N>) \<subseteq> (\<Union>i\<in>{0..<m}. negincs (\<N>s ! i))"
  proof
    fix x assume xx: "x \<in> \<Union> (negincs ` \<N>)"
    show "x \<in> (\<Union>i\<in>{0..<m}. negincs (\<N>s ! i))"
      using xx negincs_def UN_iff neg_snd_exist nodes_set_index by auto
  qed
  show "(\<Union>i\<in>{0..<m}. negincs (\<N>s ! i)) \<subseteq> \<Union> (negincs ` \<N>) "
  proof
    fix x assume xx: "x \<in> (\<Union>i\<in>{0..<m}. negincs (\<N>s ! i))"
    show "x \<in> \<Union> (negincs ` \<N>) "
      using xx negincs_def by auto
  qed
qed

lemma card_negin_index_alt: "(\<Sum>x\<in>\<N>. (neginc_num x)) =  (\<Sum>i\<in>{0..<m}. (neginc_num (\<N>s!i)))"
  by (smt (verit, ccfv_threshold) bij_betw_nodes_index sum.cong sum.reindex_bij_betw)

lemma mat_indeg_outdeg_eq:"(\<Union>x\<in>\<N>. negincs x) = (\<Union>((\<lambda>x. posincs x) `(\<N>) ))"
  using mat_indeg_union mat_outdeg_union by presburger

lemma mat_indeg_eq_sumdeg:"card (\<Union>x\<in>\<N>. negincs x) = (\<Sum>x\<in>\<N>. neginc_num x)"
proof-
  have 1: "finite \<N>" by(simp add: finite_nodes)
  then have 2:"\<forall>i\<in>{0..<m}. finite (negincs (\<N>s!i))" 
    using negincs_def by force
 then have 3: "\<forall>i\<in>{0..<m}.\<forall>k\<in>{0..<m}. i\<noteq>k \<longrightarrow> negincs (\<N>s!i) \<inter> negincs (\<N>s!k) = {}"
   using mat_negindeg_inter by simp
  have 4: "card (\<Union>x\<in>\<N>. negincs x) = card (\<Union>((negincs) `(\<N>)))"
    by simp
 also have "... = (\<Sum>x\<in>\<N>. neginc_num x)"
   using negincs_def neginc_num_def 1 2 3 card_UN_disjoint
   by (smt (verit, ccfv_SIG) mem_Collect_eq nodes_set_index sum.cong)
 thus ?thesis using 4 nodes_set_index by force
qed

lemma mat_indeg_eq_sumdeg_index:"card (\<Union>x\<in>\<N>. negincs x) = (\<Sum>i\<in>{0..<m}. (neginc_num (\<N>s!i)))"
  using card_negin_index_alt mat_indeg_eq_sumdeg by auto

lemma mat_indeg_eq_sumdeg_index_n: "(\<Sum>i\<in>{0..<m}. (neginc_num (\<N>s!i))) = n"
  using mat_indeg_cardn mat_indeg_eq_sumdeg_index by auto

lemma sum_degree_ineqout: "(\<Sum> i<m. posinc_num (\<N>s!i)) = (\<Sum> i<m. neginc_num (\<N>s!i))"
  using atLeast0LessThan mat_indeg_eq_sumdeg_index_n mat_outdeg_eq_sumdeg_index_n by auto

lemma sum_inoutdeg:"(\<Sum> i<m. posinc_num (\<N>s!i) + neginc_num (\<N>s!i)) = 2 * length \<E>s"
  by (metis atLeast0LessThan mat_outdeg_eq_sumdeg_index_n mult_2 sum.distrib sum_degree_ineqout)

lemma handshaking_for_digraph: "(\<Sum> i<m. didegree (\<N>s!i)) = 2 * length \<E>s"
  using didegree_def sum_inoutdeg by auto

text\<open>Even and odd degree\<close>

definition odd_degree_nodes where 
    "odd_degree_nodes \<equiv> {v. v \<in>\<N> \<and> odd (didegree v)}"

definition card_odd_degree_nodes where 
    "card_odd_degree_nodes  \<equiv> card (odd_degree_nodes)"

definition even_degree_nodes where 
    "even_degree_nodes  \<equiv> {v. v \<in>\<N> \<and> even (didegree v)}"

definition card_even_degree_nodes  where 
    "card_even_degree_nodes \<equiv> card (even_degree_nodes)"

lemma partition_odd_even_nodes: "{v. v \<in> \<N>} = {v. v \<in>\<N> \<and> odd (didegree v)} \<union> {v. v \<in>\<N> \<and> even (didegree v)}"
  using didegree_def by blast

lemma inter_odd_even_nodes: "{} = {v. v \<in>\<N> \<and> odd (didegree v)} \<inter> {v. v \<in>\<N> \<and> even (didegree v)}"
  using didegree_def by blast

lemma didegree_part_evenodd: "(\<Sum> v\<in>\<N>. didegree v) = (\<Sum> v\<in>(even_degree_nodes). didegree v) + (\<Sum> v\<in>(odd_degree_nodes). didegree v)" (is "?lhs =?rhs")
  using partition_odd_even_nodes inter_odd_even_nodes didegree_def even_degree_nodes_def odd_degree_nodes_def 
  by (smt (verit, del_insts) Collect_cong add.commute finite_Un finite_nodes mem_Collect_eq nodes_set_index sum.union_disjoint)

text\<open>Corollary of Handshaking lemma\<close>
lemma oddidegree_even: "even (\<Sum> v\<in>(odd_degree_nodes). didegree v)"
proof-
  have 1: "(\<Sum> v\<in>\<N>. didegree v) = 2*n"
    using handshaking_for_digraph 
    by (simp add: card_negin_index_alt card_posout_index_alt didegree_def 
       mat_indeg_eq_sumdeg_index_n mat_outdeg_eq_sumdeg_index_n sum.distrib)
  moreover have "even (\<Sum> v\<in>\<N>. didegree v)" using 1 by auto
  moreover have "even (\<Sum> v\<in>(even_degree_nodes). didegree v)"
    using even_degree_nodes_def 
    by (metis (no_types, lifting) dvd_sum mem_Collect_eq)
  ultimately show ?thesis 
    using didegree_part_evenodd by (metis even_add)
qed

end
end