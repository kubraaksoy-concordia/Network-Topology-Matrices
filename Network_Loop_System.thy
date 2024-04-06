theory Network_Loop_System
  imports  Network_Incidence_System
begin 


text \<open>This predicate provides a sequence of distinct pairs of nodes, inspired by Noschinski's graph theory\<close>
text\<open> This satisfies that there is no self loop in the network system, but it allows multi-edges\<close>

fun pred_netw_dedge_seq :: "'a node  \<Rightarrow> 'a edges \<Rightarrow> 'a node \<Rightarrow> bool" where
  " pred_netw_dedge_seq v1 [] vx = (v1 = vx)" |
  " pred_netw_dedge_seq v1 (p1 # ps) vx = (v1 = fst p1 \<and> fst p1 \<noteq> snd p1 \<and> pred_netw_dedge_seq (snd p1) ps vx)"

lemma pred_netw_path_altdef:
  assumes "ps \<noteq> []"
  shows "pred_netw_dedge_seq v1 ps vx \<longleftrightarrow> fst (hd ps) = v1 \<and> fst (hd ps) \<noteq> snd (hd ps) \<and> pred_netw_dedge_seq (snd (hd ps)) (tl ps) vx"
  using assms by(cases ps) auto

lemma assumes "ps \<noteq> []"
  shows "pred_netw_dedge_seq v1 ps vx \<Longrightarrow> hd ps = (v1, snd (hd ps))"
  using assms pred_netw_path_altdef by fastforce

definition closed_diedge_seq :: "'a node \<Rightarrow> 'a edges \<Rightarrow> bool" where
"closed_diedge_seq v1 ps \<equiv>  pred_netw_dedge_seq v1 ps v1"

definition open_diedge_seq :: "'a node \<Rightarrow> 'a edges \<Rightarrow> 'a node \<Rightarrow> bool" where
"open_diedge_seq v1 ps vx \<equiv>  pred_netw_dedge_seq v1 ps vx \<and> v1 \<noteq> vx"

text \<open>This definition is taken from the network_flow library (by Peter Lammich et al.)\<close>
definition train_nodes :: "'a node \<Rightarrow> 'a edges \<Rightarrow> 'a nodes" 
   where "train_nodes v1 ps = v1 # map snd ps"

lemma node_intrain:
"v1 \<in> set (train_nodes v1 ps)"
  using train_nodes_def 
  by (metis list.set_intros(1))

text \<open>These definitions are taken from the directed graph library (by Noschinski)\<close>
definition symcl :: "'a rel \<Rightarrow> 'a rel" ("(_\<^sup>s)" [1000] 999) where
  "symcl R = R \<union> (\<lambda>(a,b). (b,a))` R"

lemma symcl_alt: 
  fixes A :: "'a set"
  shows "R \<subseteq> A \<times> A \<longleftrightarrow> symcl R \<subseteq> A \<times> A"
  using symcl_def
  by (metis Un_subset_iff image_mono swap_product)

lemma symcl_elem: "x \<in> R \<Longrightarrow> x \<in> symcl R"
  using symcl_def by auto

primrec reverse :: "'a edges  \<Rightarrow> 'a edges" where
  "reverse [] = []" |
  "reverse (e # es) = reverse es @ [(snd e, fst e)]"

lemma reverse_append[simp]: "reverse (es @ qs) = reverse qs @ reverse es"
  by (induct es) auto

lemma reverse_reverse_list[simp]:
  "reverse (reverse es) = es"
  by (induct es) auto

lemma reverse_empty[simp]:
  "reverse es = [] \<longleftrightarrow> es = []"
  by (induct es) auto 

lemma reverse_eq: "reverse es = reverse qs \<longleftrightarrow> es = qs"
  by (metis reverse_reverse_list)

lemma edge_reverse: "e \<in> set (es) \<Longrightarrow> (snd e, fst e) \<in> set (reverse es)"
  by (induct es, auto)

(*******************************************************)
context nonempty_network_system
begin

text \<open>The below concept is a generalized concept 
that is considered both directed and semi-directed version of train (walk), path and loop (circuit)\<close>

text\<open>Edge train (walk) with no self-loop is an edge sequence with all edges appearing in the sequence are distinct\<close>

definition is_netw_gen_train :: "'a node \<Rightarrow> 'a edges \<Rightarrow> 'a node \<Rightarrow> bool" where
"is_netw_gen_train v1 ps vx \<equiv> set ps \<subseteq> symcl \<E> \<and> fst (hd ps) = v1 \<and> (snd (last ps)) = vx
                                  \<and> pred_netw_dedge_seq v1 ps vx \<and> distinct ps"

lemma is_netw_trainI: "set ps \<subseteq> symcl \<E> \<Longrightarrow> fst (hd ps) = v1 \<Longrightarrow> (snd (last ps)) = vx 
\<Longrightarrow> pred_netw_dedge_seq v1 ps vx \<Longrightarrow> distinct ps \<Longrightarrow> is_netw_gen_train v1 ps vx"
  using is_netw_gen_train_def by simp 

lemma is_netw_train_wf: "is_netw_gen_train v1 ps vx \<Longrightarrow> set ps \<subseteq> symcl \<E> \<Longrightarrow> fst (hd ps) = v1 
\<Longrightarrow> (snd (last ps)) = vx \<Longrightarrow> distinct ps"
  by (simp add: is_netw_gen_train_def)

definition is_gen_closed_train :: "'a \<Rightarrow> 'a edges \<Rightarrow> 'a \<Rightarrow> bool" where
"is_gen_closed_train v1 ps vx \<equiv> is_netw_gen_train v1 ps vx \<and> (fst (hd ps)) = (snd (last ps))"

definition is_gen_open_train :: "'a \<Rightarrow> 'a edges \<Rightarrow> 'a \<Rightarrow> bool" where
"is_gen_open_train v1 ps vx \<equiv> is_netw_gen_train v1 ps vx \<and> (fst (hd ps)) \<noteq> (snd (last ps))"


text \<open>The below describes a generalized path that allows directed or semi-directed orientation includes the case a path is a circuit, i.e , this path definition contains both open path and closed path\<close>

definition is_netw_gen_path :: "'a \<Rightarrow> 'a edges \<Rightarrow> 'a \<Rightarrow> bool" where
"is_netw_gen_path v1 ps vx \<equiv> is_netw_gen_train v1 ps vx \<and> distinct (tl (train_nodes v1 ps))"

definition is_gen_closed_path :: "'a \<Rightarrow> 'a edges \<Rightarrow> 'a \<Rightarrow> bool" where
"is_gen_closed_path v1 ps vx \<equiv> is_netw_gen_path v1 ps vx \<and> v1 = vx"

definition is_gen_open_path :: "'a \<Rightarrow> 'a edges \<Rightarrow> 'a \<Rightarrow> bool" where
"is_gen_open_path v1 ps vx \<equiv> is_netw_gen_path v1 ps vx \<and> v1 \<noteq> vx"

definition "Dpath v1 ps vx \<equiv> [e\<leftarrow>ps. is_gen_open_path v1 ps vx]"

definition open_dpath_length :: "'a \<Rightarrow> ('a \<times> 'a) list  \<Rightarrow> nat"  where
"open_dpath_length v1 ps \<equiv> length (Dpath v1 ps (snd (last ps))) - 1"

text \<open>Loop is a closed path that the first element of first Network_pair of the path is equal to second element of the last pair of the path\<close>

definition loop ::  "'a edges \<Rightarrow> bool" where
  "loop ps \<equiv> is_gen_closed_path (fst (hd ps)) ps (fst (hd ps)) \<and> (length ps \<ge> 2)"

lemma loop_altdef:
  assumes "distinct ps" and "length ps \<ge> 2" "fst (hd ps) = v1"
  shows "loop ps \<longleftrightarrow> is_gen_closed_path v1 ps v1"
proof(intro iffI)
  show "loop ps \<Longrightarrow> is_gen_closed_path v1 ps v1"
    using assms is_gen_closed_path_def loop_def by blast
  show "is_gen_closed_path v1 ps v1 \<Longrightarrow> loop ps"
    using assms by (simp add: loop_def wf_network_system)
qed

definition loop_list :: " ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
"loop_list ps = [e \<leftarrow> ps. loop ps]"

lemma loop_list_alt: "(hd ps) \<in> set (loop_list ps) \<Longrightarrow> x = fst (hd ps) \<Longrightarrow> is_gen_closed_path x ps x"
  using loop_list_def loop_def is_gen_closed_path_def by force

end

locale loop_system = nonempty_network_system +
fixes loops_list :: "'a edges list" ("\<L>s")
assumes wellformed_1: "ls \<in> set \<L>s \<Longrightarrow> set ls \<subseteq> symcl \<E> \<and> length ls \<le> length \<E>s"
assumes wellformed_2: "ls \<in> set \<L>s \<Longrightarrow> loop ls \<and> loop (reverse ls)"
and  distinct: "distinct \<L>s" 

begin

abbreviation "l \<equiv> length \<L>s"
abbreviation "\<L> \<equiv> set \<L>s"

lemma wf_loop_system: "loop_system \<N>s \<E>s \<L>s"  by intro_locales

lemma reverse_is_loop: 
  assumes "ls \<in> set \<L>s"
  shows "loop ls \<Longrightarrow> loop (reverse ls)"
  using assms wellformed_2 by auto

lemma wf_loop_system_iff: 
  assumes "ls \<in> \<L>" 
  shows "loop_system \<N>s \<E>s \<L>s \<longleftrightarrow> set ls \<subseteq> symcl \<E> \<and> loop (ls) \<and> loop (reverse ls) \<and> length ls \<le> length \<E>s"
  using wellformed_1  wellformed_2 wf_loop_system assms by blast

lemma edge_in_loop: 
  assumes "ls \<in> \<L>"
  shows "e \<in> set ls \<Longrightarrow>  e \<in> \<E> \<or> e \<in> (\<lambda>(a, b). (b, a)) `\<E> "
  using assms wellformed_1 
  by (smt (verit, best) Un_iff in_mono symcl_def)

lemma edge_in_loop_alt: 
  assumes "ls \<in> \<L>" 
  shows " e \<in> set ls \<Longrightarrow> fst e \<in> \<N> \<and> snd e \<in> \<N> \<and> fst e \<noteq> snd e"
  using assms wellformed_1 network_wf 
  by (smt (verit, ccfv_threshold) edge_in_loop imageE prod.collapse prod.simps(2) snd_conv)

lemma edge_in_rloop_alt: 
  assumes "ls \<in> \<L>" 
  shows " e \<in> set (reverse ls) \<Longrightarrow> fst e \<in> \<N> \<and> snd e \<in> \<N> \<and> fst e \<noteq> snd e"
  using assms wellformed_1 network_wf wellformed_2
  by (metis edge_in_loop_alt edge_reverse fst_eqD reverse_reverse_list snd_eqD)

lemma edge_in_ntw_in_loop: 
  assumes "ls \<in> \<L>"
  shows "e \<in> set ls \<Longrightarrow>  e \<in> \<E> \<Longrightarrow> e \<in> \<N> \<times> \<N>"
  using assms wellformed_1 
  by (metis mem_Times_iff neg_snd_exist pos_fst_exist)

lemma no_self_loop_in_symcl: 
  shows "\<And>e. e \<in> symcl \<E> \<Longrightarrow> fst e \<noteq> snd e \<and> fst e \<in> \<N> \<and> snd e \<in> \<N>"
  using Pair_inject Un_iff case_prod_beta no_self_loop symcl_def network_wf by fastforce

lemma loopedge_in_symcl:
  assumes "ls \<in> \<L>"
  shows " e \<in> (set ls \<union> set (reverse ls)) \<Longrightarrow> e \<in>  symcl \<E>"
  using assms is_gen_closed_path_def is_netw_gen_path_def is_netw_gen_train_def loop_def 
  by (metis Un_iff  sup.orderE  loop_system_axioms_def loop_system_def wf_loop_system)
  
lemma wf_node_loop: 
  shows " i < length \<L>s \<Longrightarrow> set (\<L>s!i) \<subset> \<N> \<times> \<N>"
proof
show "i < l \<Longrightarrow> set (\<L>s ! i) \<subseteq> \<N> \<times> \<N>"
  proof-
 assume i: "i < l" 
    have "\<And>x. x \<in>  set (\<L>s ! i) \<Longrightarrow> x \<in> \<N> \<times> \<N>"
      using  edge_in_loop i 
      by (metis  mem_Times_iff no_self_loop_in_symcl nth_mem subset_code(1) wellformed_1)
    then show ?thesis by auto
  qed
  show " i < l \<Longrightarrow> set (\<L>s ! i) \<noteq> \<N> \<times> \<N> "
  proof-
   assume i: "i < l" 
   have 1: "\<And>x. x \<in> set (\<L>s ! i) \<Longrightarrow> fst x \<noteq> snd x"
     using i no_self_loop no_self_loop_in_symcl edge_in_loop_alt 
      nth_mem by blast
   show ?thesis 
     by (metis "1" SigmaI edges_nempty fst_eqD last_in_set network_wf snd_conv)
 qed
qed

lemma wf_node_loop1: 
  shows " i < length \<L>s \<Longrightarrow> set (\<L>s!i) \<subseteq> symcl \<E>"
proof
show "\<And>x. i < l \<Longrightarrow> x \<in> set (\<L>s ! i) \<Longrightarrow> x \<in> \<E>\<^sup>s"
proof-
 assume i: "i < l" 
    have "\<And>x. x \<in>  set (\<L>s ! i) \<Longrightarrow> x \<in> \<E>\<^sup>s"
      using  edge_in_loop i 
      by (metis  nth_mem subset_code(1) wellformed_1)
    then show "\<And>x. i < l \<Longrightarrow> x \<in> set (\<L>s ! i) \<Longrightarrow> x \<in> \<E>\<^sup>s"
      by auto
  qed
qed

lemma edge_loop1: 
  shows "es \<in> set \<L>s \<Longrightarrow> es = loop_list es"
  by (simp add: loop_list_def wellformed_2)

lemma edge_rloop1: 
  shows "es \<in> set \<L>s \<Longrightarrow> reverse es = loop_list (reverse es)"
   by (simp add: loop_list_def wellformed_2)

lemma loop_list_alt:
  assumes "x \<in> set \<E>s"
  assumes "es \<in> set \<L>s"
  shows "x \<in> set es \<and> loop es \<and> fst x \<noteq> snd x \<longleftrightarrow> x \<in> set (loop_list es)"
  using  assms exists_nodes loop_list_def by force

lemma reverseloop_list_alt:
  assumes "x \<in> set \<E>s"
  assumes "es \<in> set \<L>s"
  shows "x \<in> set (reverse es) \<and> loop es \<and> fst x \<noteq> snd x \<longleftrightarrow> x \<in> set (loop_list (reverse es))"
  using  assms exists_nodes loop_list_def by (simp add: wellformed_2)

lemma train_nodes_rel: "es \<in> set \<L>s \<Longrightarrow> set (train_nodes (fst (hd es)) es) \<subseteq> \<N>"
  using edge_in_loop_alt loop_def  train_nodes_def wf_loop_system  wf_loop_system_iff no_self_loop_in_symcl
  by (smt (verit, ccfv_threshold) imageE list.set_map list.set_sel(1) list.size(3) nat.simps(3) numerals(2) 
            set_ConsD subset_code(1) zero_order(2))

lemma fst_loop_elem: 
  assumes "i < length \<L>s"
 shows "\<forall>e\<in> set(\<L>s!i). \<exists>v\<in>\<N>. fst e = v"
  using assms wf_node_loop by (meson edge_in_loop_alt nth_mem)

lemma snd_loop_elem:
  assumes "i < length \<L>s"
 shows "\<forall>e\<in> set(\<L>s!i). \<exists>v\<in>\<N>. snd e = v"
  using assms wf_node_loop by (meson edge_in_loop_alt nth_mem)

lemma fst_rloop_elem: 
  assumes "i < length \<L>s"
  shows "\<forall>e\<in> set (reverse (\<L>s!i)). \<exists>v\<in>\<N>. fst e = v"
  using assms wf_node_loop by (meson edge_in_rloop_alt nth_mem)

lemma snd_rloop_elem: 
  assumes "i < length \<L>s"
 shows "\<forall>e\<in> set (reverse (\<L>s!i)). \<exists>v\<in>\<N>. snd e = v"
  using assms wf_node_loop by (meson edge_in_rloop_alt nth_mem)

end

locale nonempty_loop_system = loop_system +
  assumes loops_list_nempty: " \<L>s \<noteq> []"

begin 

lemma edge_symcl: "e \<in> \<E> \<Longrightarrow> (snd e, fst e) \<in> ((\<lambda>(a, b). (b, a))`\<E>)"
  by fastforce

lemma edge_symcl_reverse: "((\<lambda>(a, b). (b, a))`\<E>) = set (reverse \<E>s) "
  using edge_reverse edge_symcl reverse_reverse_list
  by (smt (verit, del_insts) Collect_cong Collect_mem_eq case_prodE case_prod_eta fst_conv imageE mem_Collect_eq old.prod.case  snd_conv)

lemma edge_in_loop_pos_inci_node: 
  assumes  "ls \<in> \<L>" 
  shows "\<exists>e \<in> set ls. \<exists>x \<in> set (train_nodes (fst (hd ls)) ls). fst e = x"
proof-
  have 1 : "set ls \<subseteq> symcl \<E>" using wellformed_1 assms(1) by simp 
  have 2: "set (train_nodes (fst (hd ls)) ls) \<subseteq> \<N> " 
    using assms train_nodes_rel  by auto
  from 1 obtain e where "e \<in> set ls" and "e \<in> symcl \<E>" using 1 assms 
    by (metis in_mono le_zero_eq list.set_sel(1) list.size(3) nat.simps(3) loop_def numerals(2) wellformed_2)
  hence 5: "\<exists>e \<in> set ls. \<exists>x\<in>set (train_nodes (fst (hd ls)) ls). fst e = x"
     unfolding train_nodes_def using assms 1 2 wellformed_1 
     by (metis empty_iff list.set(1) list.set_sel(1) node_intrain train_nodes_def)
   thus ?thesis by auto
 qed

lemma pos_node_in_edge_in_loop: 
  assumes  "ls \<in> \<L>" 
  shows "\<exists>e \<in> set ls. \<exists>x \<in> \<N>. fst e = x"
  by (meson assms edge_in_loop_pos_inci_node in_mono train_nodes_rel)

lemma index_pos_node_in_edge_in_loop: 
  assumes  "ls \<in> \<L>" "x \<in> set ls"
  obtains i  where "x = (ls!i) \<and> fst x \<in> \<N> \<and> i < length ls"  
  using assms in_set_conv_nth
  by (metis (mono_tags, lifting) in_mono wellformed_1 no_self_loop_in_symcl) 

lemma index_pos_node_in_edge_in_loop1: 
  assumes  "ls \<in> \<L>" "y \<in>  set ls" "pos_incident x y" 
  obtains i j  where "y = (ls!i) \<and> fst y = x \<and> i < length ls"  
  using assms in_set_conv_nth
  by (metis (mono_tags, lifting) I\<^sub>P_def Product_Type.Collect_case_prodD fst_conv pos_incident_def snd_conv)

lemma edge_in_loop_neg_inci_node: 
  assumes  "ls \<in> \<L>" 
  shows "\<exists>e \<in> set ls. \<exists>x \<in> set (train_nodes (fst (hd ls)) ls). snd e = x"
  unfolding train_nodes_def using assms
  by (metis imageI image_set list.set_intros(2) edge_in_loop_pos_inci_node)

lemma neg_node_in_edge_in_loop: 
  assumes  "ls \<in> \<L>" 
  shows "\<exists>e \<in> set ls. \<exists>x \<in> \<N>. snd e = x"
  by (meson assms edge_in_loop_neg_inci_node in_mono train_nodes_rel)

lemma edge_in_loop_posorneg_inci_node: 
  assumes  "ls \<in> \<L>"  and "x \<in> set (train_nodes (fst (hd ls)) ls)"
  shows "\<exists>e1 e2. fst e1 = x \<and> snd e2 = x \<and> e1 \<noteq> e2"
  using assms edge_in_loop_neg_inci_node edge_in_loop_pos_inci_node 
     no_self_loop_in_symcl wellformed_1 wf_loop_system by fastforce

lemma edge_in_loop_posneg_inc: 
 assumes  "ls \<in> \<L>"  and "x \<in> \<N>"
  shows "\<exists>e1 e2. fst e1 = x \<and> snd e2 = x \<and> e1 \<noteq> e2"
  using assms edge_in_loop_alt neg_node_in_edge_in_loop by fastforce

lemma wf_loop_nempty_alt: "\<forall>k \<in> {0..<length \<L>s}.  \<L>s!k \<notin> {}"
  by blast

lemma wf_edges_nempty_alt: "\<forall>k \<in> {0..<length \<L>s}. (\<forall>j \<in> {0..<length \<E>s}. \<L>s!k!j \<notin> {})"
  by blast

lemma loop_indexing_inj: "\<forall> k \<in> H . k < length \<L>s \<Longrightarrow> inj_on ((!) \<L>s) H"
  using distinct inj_on_nth by blast

lemma wf_loop_edge : "\<forall>k \<in> {0..<length \<L>s}.  set (\<L>s!k) \<subseteq> symcl \<E>"
  using wellformed_1 by auto

lemma len_loop_edge: "\<forall>k \<in> {0..<length \<L>s}.  length (\<L>s!k) \<le> length \<E>s"
  using wellformed_1 by auto

lemma loop_distinct: "\<forall>k \<in> {0..<length \<L>s}. distinct (\<L>s!k)"
  using is_gen_closed_path_def is_netw_gen_path_def is_netw_gen_train_def loop_def wellformed_1 wellformed_2  by auto

text \<open>Basic properties on loop_system \<close>

lemma loop_list_length: "length \<L>s = l"
  by simp

lemma valid_edges_index_cons: 
  shows "p \<in> set ls \<Longrightarrow> \<exists> k. ls ! k = p \<and> k < length ls"
  by (meson in_set_conv_nth)

lemma valid_edges_posneg: 
  assumes "ls \<in>  \<L>" 
  shows "p \<in> set ls \<Longrightarrow> p \<in> set (loop_list ls) \<or> p \<in> set (loop_list (reverse ls))"
  using assms edge_loop1 by auto

lemma valid_loops_index: "i < l \<Longrightarrow> \<L>s ! i \<in> \<L>"
  using loop_list_length by (metis nth_mem)

lemma valid_loops_index_cons: "ls \<in> \<L> \<Longrightarrow> \<exists> i . \<L>s ! i = ls \<and> i < l"
  by (auto simp add: set_conv_nth)

lemma valid_loops_index_index: " k < length (\<L>s ! i) \<Longrightarrow>  \<L>s ! i ! k \<in> set (\<L>s ! i)"
  by auto

lemma valid_loops_index_index_cons: "p \<in> set (\<L>s ! i)  \<Longrightarrow> \<exists> k . \<L>s ! i ! k = p \<and> k < length (\<L>s ! i) "
  by (meson in_set_conv_nth)

lemma valid_loops_symcl: "p \<in> set (\<L>s ! i) \<and> i < length \<L>s \<Longrightarrow> p \<in> symcl \<E>"
  using nth_mem wellformed_1 by fastforce

lemma edge_in_valid_loop: "p \<in> set (\<L>s ! i) \<and> i < length \<L>s \<Longrightarrow> fst p \<noteq> snd p"
  using no_self_loop_in_symcl valid_loops_symcl by blast

lemma sedge_in_valid_loop: "p \<in> set (\<L>s ! i) \<and> i < length \<L>s \<Longrightarrow> p \<in> \<E>  \<or> p \<in> (\<lambda>(a, b). (b, a)) `\<E> "
  using valid_loops_symcl  edge_in_loop nth_mem by blast

lemma valid_loops_index_obtains: 
  assumes "ls \<in> \<L>"
  obtains i where  "\<L>s ! i = ls \<and> i < l"
  using assms valid_loops_index_cons by auto
            
lemma loops_set_image: "\<L> = image (\<lambda> i. (\<L>s!i)) ({0..<l})"
  by (metis list.set_map map_nth set_upt)

lemma loops_set_list_image: 
  assumes "i < l" 
  shows "set (\<L>s ! i) = image (\<lambda> k. (\<L>s!i!k)) ({0..<length (\<L>s!i)})"
  using distincts by (metis list.set_map map_nth set_upt)

lemma valid_edgeinloop_index_obtains: 
  assumes "x \<in> set (\<L>s!i)" 
  obtains k where "\<L>s ! i ! k = x \<and> k < length (\<L>s!i)"
  using assms valid_loops_index_index_cons by presburger

lemma valid_edgeinloop_index_obtains1: 
  assumes "ls \<in> set \<L>s" "x \<in> set ls"
  obtains k where "ls ! k = x \<and> k < length ls"
  using assms 
  by (meson valid_edges_index_cons)

lemma bij_betw_joints_index: "bij_betw (\<lambda> k. \<L>s ! k) {0..<l} \<L>"
proof (simp add: bij_betw_def, intro conjI)
  show "inj_on ((!) \<L>s) {0..<l}"
    by(simp add: loop_indexing_inj)
  show "(!) \<L>s ` {0..<l} =  \<L>"
    using loops_set_image by presburger
qed

lemma valid_edg_inl: 
  assumes "i< length \<L>s" 
  obtains k where "\<E>s ! k \<in> set (\<L>s ! i)" "k < length \<E>s"
  using assms oops

text \<open>The loop-edge relationship with orientation and its properties\<close>    

definition "L\<^sub>p \<equiv> {(x, es). x \<in> set \<E>s \<and> es \<in> set \<L>s \<and> x \<in> set (loop_list es)}"   (*positively oriented loop*)

definition "L\<^sub>n \<equiv> {(x, es) . x \<in> (set \<E>s) \<and> es \<in> set \<L>s \<and> x \<in> set (loop_list (reverse es)) \<and>  x \<notin> set (loop_list es)}" (*negatively oriented loop*)

definition in_neg_loop :: "'a \<times> 'a \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool"  where
"in_neg_loop x es \<equiv> (x, es) \<in> L\<^sub>n"

definition in_pos_loop :: "'a \<times> 'a \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool" where
"in_pos_loop x es \<equiv> (x, es) \<in> L\<^sub>p"

lemma loop_set:
  shows  "x \<in> set es \<and> loop es \<longleftrightarrow> x \<in> set (loop_list es)"
  using loop_list_def by auto

lemma loop_rev_set:
  assumes "es \<in> (set \<L>s)"
  shows  "x \<in> set (reverse es) \<and> loop (reverse es) \<longleftrightarrow> x \<in> set (reverse (loop_list es))"
  using assms L\<^sub>n_def wellformed_1 loop_def loop_list_def  wellformed_2
  by (smt (verit, best) edge_loop1)

lemma in_neg_loop: 
  assumes "x \<in> (set \<E>s)"
  assumes "es \<in> \<L>" 
  shows "in_neg_loop x es \<longleftrightarrow> x \<in> set (loop_list (reverse (es))) \<and> x \<notin> set (loop_list es)"
  using assms by (simp add: L\<^sub>n_def in_neg_loop_def)

lemma in_pos_loop: 
  assumes "x \<in> set \<E>s"
  assumes "es \<in> set \<L>s"
  shows "in_pos_loop x es \<longleftrightarrow> x \<in> set (loop_list es) "
  using assms by (simp add: L\<^sub>p_def in_pos_loop_def)

lemma not_inpos_inneg_loop: 
  assumes "x \<in> set \<E>s"
  assumes "es \<in> set \<L>s"
  shows " \<not> in_neg_loop x es \<and> \<not>in_pos_loop x es \<longleftrightarrow> (x \<notin> set (loop_list es) \<and> x \<notin>  set (loop_list (reverse es)))"
  using assms in_pos_loop in_neg_loop  edge_loop1 edge_rloop1 by auto

lemma not_inpos_inneg_loop': 
  assumes "x \<in> set \<E>s"
  assumes "es \<in> set \<L>s"
  shows " \<not> in_neg_loop x es \<and> \<not>in_pos_loop x es \<longleftrightarrow> x \<notin> set es \<and>  x \<notin>  set (reverse (es))"
  using assms edge_loop1 no_self_loop not_inpos_inneg_loop reverseloop_list_alt wellformed_2 by auto

lemma wf_pos_loop: 
  shows "in_pos_loop x es \<longrightarrow> loop es \<and> x \<in> set es"
  by (simp add: L\<^sub>p_def in_pos_loop_def loop_list_def) 

lemma wf_pos_loop_iff:
  assumes "es \<in> set \<L>s" "x \<in> set \<E>s"
  shows "in_pos_loop x es \<longleftrightarrow> loop es \<and> x \<in> set es"
  using assms edge_loop1 in_pos_loop wellformed_2 by simp
 
lemma wf_neg_loop:
  shows "in_neg_loop x es \<longrightarrow> x \<in> set (reverse es) \<and> x \<notin> set es"  
  using L\<^sub>n_def edge_rloop1 in_neg_loop_def edge_loop1 by auto

lemma wf_neg_loop_iff:
  assumes "es \<in> set \<L>s" "x \<in> set \<E>s"
  shows "in_neg_loop x es \<longleftrightarrow> x \<in> set (reverse es) \<and> x \<notin> set es"  
  using assms in_neg_loop edge_loop1 edge_rloop1 by auto

lemma in_loop_not_samepos_directed:
  assumes  "x \<in> \<E>" and "es \<in> set \<L>s" 
shows "\<not> in_pos_loop x es \<Longrightarrow> x \<notin> set (loop_list es) \<and> (x \<in> set (loop_list (reverse es)) \<or> x \<notin> set (loop_list (reverse es)))"
  using in_pos_loop_def L\<^sub>p_def assms by blast

lemma in_loop_not_oppositeneg_directed:
  assumes "x \<in> \<E>" and "es \<in> set \<L>s"
  shows "\<not> in_neg_loop x es \<Longrightarrow>  in_pos_loop x es \<Longrightarrow> x \<in> set (loop_list es)"
  using in_neg_loop_def L\<^sub>n_def assms edge_loop1 in_pos_loop by fastforce

lemma neg_loop_cond_indexed[simp]: "k < l \<Longrightarrow> j < n \<Longrightarrow> (\<E>s ! j) \<notin> set (loop_list (\<L>s ! k)) 
\<Longrightarrow> in_neg_loop (\<E>s ! j) (\<L>s ! k) \<longleftrightarrow> (\<E>s ! j) \<in> set (loop_list (reverse (\<L>s ! k)))"
  using in_neg_loop valid_edges_index valid_loops_index by blast

lemma pos_loop_cond_indexed[simp]: "k < l \<Longrightarrow> j < n \<Longrightarrow> fst (\<E>s ! j) \<noteq> snd (\<E>s ! j) 
\<Longrightarrow> (\<E>s ! j) \<notin> set (reverse (loop_list (\<L>s ! k)))  \<Longrightarrow> in_pos_loop (\<E>s ! j) (\<L>s ! k) \<longleftrightarrow> (\<E>s ! j) \<in> set (\<L>s ! k)"
  using valid_edges_index valid_loops_index edge_loop1 in_pos_loop by presburger

lemma in_loop_not_samepos_directed_cond_indexed: "k < l \<Longrightarrow> j < n  \<Longrightarrow> fst (\<E>s ! j) \<noteq> snd (\<E>s ! j)
 \<Longrightarrow> in_neg_loop (\<E>s ! j) (\<L>s ! k)  \<Longrightarrow> (\<not> in_pos_loop (\<E>s ! j) (\<L>s ! k)) \<longleftrightarrow> (\<E>s ! j) \<notin> set (loop_list (\<L>s ! k)) \<and> (\<E>s ! j) \<in> set (loop_list (reverse (\<L>s ! k))) "
  using in_neg_loop valid_edges_index valid_loops_index in_pos_loop by blast

lemma not_in_loop_indexed: "k< l \<Longrightarrow> j < n \<Longrightarrow> \<not> (in_pos_loop (\<E>s ! j) (\<L>s ! k))  \<Longrightarrow> \<not> in_neg_loop (\<E>s ! j) (\<L>s ! k)  \<Longrightarrow> (\<E>s ! j) \<notin> set (reverse (\<L>s ! k)) \<and> (\<E>s ! j) \<notin> set (\<L>s ! k)"
  using  wellformed_2 by (metis filter_True in_loop_not_samepos_directed loop_list_def in_neg_loop nth_mem)

lemma in_loop_not_neg_cond_indexed1: "k < l \<Longrightarrow> j < n \<Longrightarrow>  \<not> in_neg_loop (\<E>s ! j) (\<L>s ! k) \<Longrightarrow> in_pos_loop (\<E>s ! j) (\<L>s ! k) \<Longrightarrow> (\<E>s ! j) \<in>  set (\<L>s ! k)"
  using wf_loop_system wf_pos_loop by blast

lemma node_in_pos_loop: " k<l \<Longrightarrow> j < n \<Longrightarrow> in_pos_loop (\<E>s ! j) (\<L>s ! k) \<Longrightarrow> (\<exists>i1 i2. i1 < m \<and> i2 <m \<and> (\<N>s!i1 = fst (\<E>s ! j) \<and> \<N>s!i2 = snd (\<E>s ! j)) \<and> (\<E>s ! j) \<in>  set (\<L>s ! k)) " 
  by (metis edges_valid_nodes_index1 fst_conv wf_pos_loop snd_conv)

lemma node_in_neg_loop: " k<l \<Longrightarrow> j < n \<Longrightarrow> in_neg_loop (\<E>s ! j) (\<L>s ! k) \<Longrightarrow> (\<exists>i1 i2. i1 < m \<and> i2 <m \<and> (\<N>s!i1 = fst (\<E>s ! j) \<and> \<N>s!i2 = snd (\<E>s ! j)) \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! k))) \<and> (\<E>s ! j) \<notin> set (\<L>s ! k) " 
  by (metis edges_valid_nodes_index1 fst_conv wf_neg_loop snd_conv)

lemma neg_loop_posincident: 
  shows "in_neg_loop x es \<Longrightarrow> pos_incident (fst x) x \<and> neg_incident (snd x) x"
  using in_neg_loop 
  by (simp add: L\<^sub>n_def in_neg_loop_def neg_incident_netw_altdef pos_incident_netw_altdef)

lemma pos_loop_posincident: 
  shows "in_pos_loop x es \<Longrightarrow> pos_incident (fst x) x \<and> neg_incident (snd x) x"
  using in_pos_loop
  by (simp add: L\<^sub>p_def in_pos_loop_def neg_incident_netw_altdef pos_incident_netw_altdef)

text\<open>Relationship between incident of node-edge and loop-edge\<close>

lemma pos_loop_pos_inc_indexed: "i < length (\<L>s ! k) \<Longrightarrow> k < l \<Longrightarrow> j < n \<Longrightarrow> in_pos_loop (\<E>s ! j) (\<L>s ! k) 
\<Longrightarrow> pos_incident (fst (\<L>s ! k ! i)) (\<E>s ! j) \<Longrightarrow>  fst (\<E>s ! j) = fst (\<L>s! k! i) \<and> (\<E>s ! j) \<in> set (\<L>s ! k) "
  using in_pos_loop pos_incident_netw_altdef wf_pos_loop nth_mem by blast

lemma pos_loop_neg_inc_indexed: "i < length (\<L>s ! k) \<Longrightarrow> k < l \<Longrightarrow> j < n \<Longrightarrow> in_pos_loop (\<E>s ! j) (\<L>s ! k) 
\<Longrightarrow> neg_incident (snd (\<L>s ! k ! i)) (\<E>s ! j) \<Longrightarrow>  snd (\<E>s ! j) = snd (\<L>s! k! i) \<and> (\<E>s ! j) \<in> set (\<L>s ! k) "
  using in_pos_loop neg_incident_netw_altdef wf_neg_loop nth_mem  node_in_pos_loop by blast

lemma neg_loop_pos_inc_indexed: "i < length (\<L>s ! k) \<Longrightarrow> k < l \<Longrightarrow> j < n \<Longrightarrow> in_neg_loop (\<E>s ! j) (\<L>s ! k) 
\<Longrightarrow> pos_incident (fst (\<L>s ! k ! i)) (\<E>s ! j) \<Longrightarrow>  fst (\<E>s ! j) = fst (\<L>s! k! i) \<and> (\<E>s ! j) \<notin> set (\<L>s ! k) \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! k))"
   by (simp add: pos_incident_netw_altdef wf_neg_loop)

lemma neg_loop_neg_inc_indexed: "i < length (\<L>s ! k) \<Longrightarrow> k < l \<Longrightarrow> j < n \<Longrightarrow> in_neg_loop (\<E>s ! j) (\<L>s ! k) 
\<Longrightarrow> neg_incident (snd (\<L>s ! k ! i)) (\<E>s ! j) \<Longrightarrow>  snd (\<E>s ! j) = snd (\<L>s! k! i) \<and> (\<E>s ! j) \<notin> set (\<L>s ! k) \<and> (\<E>s ! j) \<in> set (reverse (\<L>s ! k))"
   by (simp add: neg_incident_netw_altdef wf_neg_loop)

lemma pos_loop_pos_inci:
  assumes  "x \<in> \<E>" and "es \<in> set \<L>s"
  shows "in_pos_loop x es \<Longrightarrow> pos_incident y x \<Longrightarrow> fst x = y \<and> x \<in> set (loop_list es)"
  by (simp add: assms in_pos_loop pos_incident_netw_altdef)

lemma pos_loop_neg_inci:
  assumes  "x \<in> \<E>" and "es \<in> set \<L>s"
  shows "in_pos_loop x es \<Longrightarrow> neg_incident y x \<Longrightarrow> snd x = y \<and> x \<in> set (loop_list es)"
  by (simp add: assms in_pos_loop neg_incident_netw_altdef)

lemma nnodein_pos_loop:
  assumes  "x \<in> \<E>" and "es \<in> set \<L>s"
  shows "in_pos_loop x es \<Longrightarrow> neg_incident y x \<Longrightarrow> y \<in> set (train_nodes (snd x) (loop_list es))"
  by (metis assms imageI in_pos_loop list.set_intros(2) list.set_map neg_incident_netw_altdef train_nodes_def)
  
lemma pnodein_pos_loop:
  assumes  "x \<in> \<E>" 
  shows "pos_incident y x \<Longrightarrow> in_pos_loop x es \<Longrightarrow> y \<in> set (train_nodes (fst x) es)"
  by (simp add: assms node_intrain pos_incident_netw_altdef)  

lemma neg_loop_pos_inci:
  assumes  "x \<in> \<E>"
  shows " pos_incident y x \<Longrightarrow> in_neg_loop x es \<Longrightarrow> fst x = y \<and> x \<notin> set es \<and> x \<in> set (reverse es)"
  by (simp add: assms pos_incident_netw_altdef wf_neg_loop)

lemma neg_loop_neg_inci:
  assumes  "x \<in> \<E>" 
  shows "neg_incident y x \<Longrightarrow> in_neg_loop x es \<Longrightarrow> snd x = y \<and> x \<notin> set es \<and> x \<in> set (reverse es)"
  using assms neg_incident_netw_altdef wf_neg_loop by blast

lemma neg_loop_pnode:
  assumes  "x \<in> \<E>" 
  shows "in_neg_loop x es \<Longrightarrow> pos_incident y x \<Longrightarrow> y \<in> set (train_nodes (fst x) (loop_list (reverse es)))"
  by (simp add: assms node_intrain pos_incident_netw_altdef)
  
lemma nnodein_neg_loop:
  assumes  "x \<in> \<E>" 
  shows " neg_incident y x \<Longrightarrow> in_neg_loop x es \<Longrightarrow> y \<in> set (train_nodes (snd x) (loop_list (reverse es)))"
  by (simp add: assms neg_incident_netw_altdef node_intrain)

lemma swapreverse: "e \<in> \<E> \<Longrightarrow>  swapair e \<in> set (reverse \<E>s)"
proof-
  assume "e \<in> \<E> "
  then have  "(snd e, fst e) \<in> set (reverse \<E>s)"
    using edge_reverse by fastforce
  thus ?thesis by auto
qed

lemma "e \<in> set (reverse ls) \<longleftrightarrow> swapair e \<in> set ls"
proof
  show "e \<in> set (reverse ls) \<Longrightarrow> swapair e \<in> set ls"
  proof-
    assume "e \<in> set (reverse ls)"
    then show "swapair e \<in> set ls"
      by (metis edge_reverse reverse_reverse_list swapair.elims)
  qed
  show " swapair e \<in> set ls \<Longrightarrow> e \<in> set (reverse ls)"
  proof-
    assume "swapair e \<in> set ls"
    then show "e \<in> set (reverse ls)"
      using edge_reverse by fastforce
  qed
qed

end
end

