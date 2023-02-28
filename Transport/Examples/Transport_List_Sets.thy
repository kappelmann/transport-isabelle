\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Transport Between Lists and Sets\<close>
theory Transport_List_Sets
  imports
    Transport_PER
    Transport_Syntax
    "HOL-Library.FSet"
begin

paragraph \<open>Summary\<close>
text \<open>Introductory examples from the Transport paper. Transports between lists
and (finite) sets.  Refer to the paper for more details.\<close>

paragraph \<open>Introductory examples from paper\<close>

context
  includes transport_syntax
begin

text \<open>Left and right relations.\<close>

definition "L1 xs xs' \<equiv> fset_of_list xs = fset_of_list xs'"
abbreviation (input) "(Rfin :: 'a fset \<Rightarrow> _) \<equiv> (=)"
definition "L2 xs xs' \<equiv> set xs = set xs'"
abbreviation (input) "(R :: 'a set \<Rightarrow> _) \<equiv> (=\<^bsub>finite :: 'a set \<Rightarrow> bool\<^esub>)"

context
  includes galois_rel_syntax
begin

interpretation t : transport L2 R l r for L2 R l r .

text \<open>Proofs of equivalences.\<close>

lemma list_fset_PER [per_intro]:
  "(L1 \<equiv>\<^bsub>PER\<^esub> Rfin) fset_of_list sorted_list_of_fset"
  unfolding L1_def by fastforce

lemma list_set_PER [per_intro]: "(L2 \<equiv>\<^bsub>PER\<^esub> R) set sorted_list_of_set"
  unfolding L2_def by fastforce

text \<open>We can rewrite the Galois relators in the following theorems to
the relator of the paper.\<close>

definition "LFS xs s \<equiv> fset_of_list xs = s"
definition "LS xs s \<equiv> set xs = s"

lemma list_fset_Galois_eq: "(\<^bsub>L1\<^esub>\<lessapprox>\<^bsub>Rfin sorted_list_of_fset\<^esub>) \<equiv> LFS"
  unfolding LFS_def L1_def by (intro eq_reflection ext) (auto)
lemma list_fset_Galois_eq_symm: "(\<^bsub>Rfin\<^esub>\<lessapprox>\<^bsub>L1 fset_of_list\<^esub>) \<equiv> LFS\<inverse>"
  unfolding LFS_def L1_def by (intro eq_reflection ext) (auto)
lemma list_set_Galois_eq: "(\<^bsub>L2\<^esub>\<lessapprox>\<^bsub>R sorted_list_of_set\<^esub>) \<equiv> LS"
  unfolding LS_def L2_def by (intro eq_reflection ext) (auto)

declare list_fset_Galois_eq[transport_relator_rewrite, unif_hint]
  list_fset_Galois_eq_symm[transport_relator_rewrite, unif_hint]
  list_set_Galois_eq[transport_relator_rewrite, unif_hint]

end

(*unification hint*)
lemma L1_eq_L2 [unif_hint]: "L1 \<equiv> L2"
  unfolding L1_def L2_def
  by (intro eq_reflection ext) (auto simp: fset_of_list_elem)

definition "max_list xs \<equiv> foldr max xs (0 :: nat)"

text \<open>Proof of parametricity for @{term max_list}.\<close>

lemma max_max_list_removeAll_eq_maxlist:
  assumes "x \<in> set xs"
  shows "max x (max_list (removeAll x xs)) = max_list xs"
  unfolding max_list_def using assms by (induction xs)
  (simp_all, (metis max.left_idem removeAll_id max.left_commute)+)

lemma max_list_parametric [transport_parametric]:
  "(L2 \<Rrightarrow> (=)) max_list max_list"
proof (intro Dep_Fun_Rel_relI)
  fix xs xs' :: "nat list" assume "L2 xs xs'"
  then have "finite (set xs)" "set xs = set xs'" unfolding L2_def by auto
  then show "max_list xs = max_list xs'"
  proof (induction "set xs"  arbitrary: xs xs' rule: finite_induct)
    case (insert x F)
    then have "F = set (removeAll x xs)" by auto
    moreover from insert have "... = set (removeAll x xs')" by auto
    ultimately have "max_list (removeAll x xs) = max_list (removeAll x xs')"
      (is "?lhs = ?rhs") using insert by blast
    then have "max x ?lhs = max x ?rhs" by simp
    then show ?case
      using insert max_max_list_removeAll_eq_maxlist insertI1 by metis
  qed auto
qed

lemma max_list_parametricfin [transport_parametric]:
  "(L1 \<Rrightarrow> (=)) max_list max_list"
  using max_list_parametric by (simp only: L1_eq_L2)

text \<open>Transport from lists to finite sets.\<close>

transport_term max_fset :: "nat fset \<Rightarrow> nat" where x = max_list
  by transport_term_prover

text \<open>Use @{command print_theorems} to show all theorems.\<close>
(*print_theorems*)

lemma "(LFS \<Rrightarrow> (=)) max_list max_fset" by (fact max_fset_related')

lemma [transport_parametric]: "(Rfin \<Rrightarrow> (=)) max_fset max_fset"
  by simp

text \<open>Transport from lists to sets.\<close>

transport_term max_set :: "nat set \<Rightarrow> nat" where x = max_list
  by transport_term_prover

lemma "(LS \<Rrightarrow> (=)) max_list max_set" by (fact max_set_related')

text \<open>The registration of symmetric equivalence rules is not done by default as
of now, but that would not be a problem in principle.\<close>

lemma list_fset_PER_sym [per_intro]:
  "(Rfin \<equiv>\<^bsub>PER\<^esub> L1) sorted_list_of_fset fset_of_list"
  by (subst transport.partial_equivalence_rel_equivalence_right_left_iff_partial_equivalence_rel_equivalence_left_right)
  (fact list_fset_PER)

text \<open>Transport from finite sets to lists.\<close>

transport_term max_list' :: "nat list \<Rightarrow> nat" where x = max_fset
  by transport_term_prover

lemma "(LFS\<inverse> \<Rrightarrow> (=)) max_fset max_list'" by (fact max_list'_related')


text \<open>Transporting higher-order functions.\<close>

lemma map_parametric [transport_parametric]:
  "(((=) \<Rrightarrow> (=)) \<Rrightarrow> L2 \<Rrightarrow> L2) map map"
  unfolding L2_def
  by (intro Dep_Fun_Rel_relI) simp

(*sorted_list_of_fset requires a linorder*)
(*in theory, we could use a different transport function to avoid that constraint*)
transport_term map_set :: "('a :: linorder \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('b :: linorder) set"
  where x = "map :: ('a :: linorder \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> ('b :: linorder) list"
  by transport_term_prover

lemma "(((=) \<Rrightarrow> (=)) \<Rrightarrow> LS \<Rrightarrow> LS) map map_set" by (fact map_set_related')


lemma filter_parametric [transport_parametric]:
  "(((=) \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> L2 \<Rrightarrow> L2) filter filter"
  unfolding L2_def by (intro Dep_Fun_Rel_relI) simp

transport_term filter_set :: "('a :: linorder \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where x = "filter :: ('a :: linorder \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  by transport_term_prover

lemma "(((=) \<Rrightarrow> (=)) \<Rrightarrow> LS \<Rrightarrow> LS) filter filter_set"
  by (rule filter_set_related')

lemma append_parametric [transport_parametric]:
  "(L2 \<Rrightarrow> L2 \<Rrightarrow> L2) append append"
  unfolding L2_def by (intro Dep_Fun_Rel_relI) simp

transport_term append_set :: "('a :: linorder) set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where x = "append :: ('a :: linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  by transport_term_prover

lemma "(LS \<Rrightarrow> LS \<Rrightarrow> LS) append append_set"
  by (rule append_set_related')

text \<open>The prototype also provides a simplified definition.\<close>
lemma "append_set s s' \<equiv> set (sorted_list_of_set s) \<union> set (sorted_list_of_set s')"
  by (fact append_set_app_eq)

lemma "finite s \<Longrightarrow> finite s' \<Longrightarrow> append_set s s' = s \<union> s'"
  by (auto simp: append_set_app_eq)

end


end