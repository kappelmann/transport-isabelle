theory Transport_Typedef
  imports
    Main
    Transport_Typedef_Base
    Transport_PER
    Transport_Syntax
begin

context
  includes galois_rel_syntax transport_syntax
begin

typedef pint = "{i :: int. 0 \<le> i}" by auto

interpretation typedef_pint : type_definition Rep_pint Abs_pint "{i :: int. 0 \<le> i}"
  by (fact type_definition_pint)

lemma [transport_relator_rewrite, unif_hint]:
  "(\<^bsub>(=\<^bsub>Collect ((\<le>) (0 :: int))\<^esub>)\<^esub>\<lessapprox>\<^bsub>(=) Rep_pint\<^esub>) \<equiv> typedef_pint.AR"
  using typedef_pint.left_Galois_eq_AR by (intro eq_reflection) simp

typedef 'a fset = "{s :: 'a set. finite s}" by auto

interpretation typedef_fset :
  type_definition Rep_fset Abs_fset "{s :: 'a set. finite s}"
  by (fact type_definition_fset)

lemma [transport_relator_rewrite, unif_hint]:
  "(\<^bsub>(=\<^bsub>{s :: 'a set. finite s}\<^esub>) :: 'a set \<Rightarrow> _\<^esub>\<lessapprox>\<^bsub>(=) Rep_fset\<^esub>) \<equiv> typedef_fset.AR"
  using typedef_fset.left_Galois_eq_AR by (intro eq_reflection) simp

lemma eq_restrict_set_eq_eq_unif_hint [unif_hint]:
  "P \<equiv> \<lambda>x. x \<in> A \<Longrightarrow> ((=\<^bsub>A :: 'a set\<^esub>) :: 'a \<Rightarrow> _) \<equiv> (=\<^bsub>P\<^esub>)"
  by simp

(*could also automatically tagged for every instance in type_definition*)
declare
  typedef_pint.partial_equivalence_rel_equivalence[per_intro]
  typedef_fset.partial_equivalence_rel_equivalence[per_intro]


lemma one_parametric [transport_in_dom]: "typedef_pint.L 1 1" by auto

transport_term pint_one :: "pint" where x = "1 :: int"
  by transport_prover

lemma add_parametric [transport_in_dom]:
  "(typedef_pint.L \<Rrightarrow> typedef_pint.L \<Rrightarrow> typedef_pint.L) (+) (+)"
  by (intro Dep_Fun_Rel_relI) (auto intro!: eq_restrictI elim!: eq_restrictE)

transport_term pint_add :: "pint \<Rightarrow> pint \<Rightarrow> pint"
  where x = "(+) :: int \<Rightarrow> _"
  by transport_prover

lemma empty_parametric [transport_in_dom]: "typedef_fset.L {} {}"
  by auto

transport_term fempty :: "'a fset" where x = "{} :: 'a set"
  by transport_prover


lemma insert_parametric [transport_in_dom]:
  "((=) \<Rrightarrow> typedef_fset.L \<Rrightarrow> typedef_fset.L) insert insert"
  by auto

transport_term finsert :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where x = insert
  and L = "((=) \<Rrightarrow> typedef_fset.L \<Rrightarrow> typedef_fset.L)"
  and R = "((=) \<Rrightarrow> typedef_fset.R \<Rrightarrow> typedef_fset.R)"
  by transport_prover

context
  notes refl[transport_related_intro]
begin

transport_term insert_add_int_fset_whitebox :: "int fset"
  where x = "insert (1 + (1 :: int)) {}" !
  by transport_whitebox_prover

lemma empty_parametric' [transport_related_intro]: "(rel_set R) {} {}"
  by (intro Dep_Fun_Rel_relI rel_setI) (auto dest: rel_setD1 rel_setD2)

lemma insert_parametric' [transport_related_intro]:
  "(R \<Rrightarrow> rel_set R \<Rrightarrow> rel_set R) insert insert"
  by (intro Dep_Fun_Rel_relI rel_setI) (auto dest: rel_setD1 rel_setD2)

(*proven for all natural functors*)
lemma Galois_set_hint [unif_hint]:
  "L \<equiv> rel_set (L1 :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Longrightarrow> R \<equiv> rel_set (R1 :: 'b \<Rightarrow> 'b \<Rightarrow> bool)
  \<Longrightarrow> r \<equiv> image r1 \<Longrightarrow> S \<equiv> (\<^bsub>L1\<^esub>\<lessapprox>\<^bsub>R1 r1\<^esub>) \<Longrightarrow> (\<^bsub>L\<^esub>\<lessapprox>\<^bsub>R r\<^esub>) \<equiv> rel_set S"
  sorry

transport_term insert_add_pint_set_whitebox :: "pint set"
  where x = "insert (1 + (1 :: int)) {}" !
  by transport_whitebox_prover

print_statement insert_add_int_fset_whitebox_def insert_add_pint_set_whitebox_def

end

lemma image_parametric [transport_in_dom]:
  "(((=) \<Rrightarrow> (=)) \<Rrightarrow> typedef_fset.L \<Rrightarrow> typedef_fset.L) image image"
  by (intro Dep_Fun_Rel_relI) auto

transport_term fimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset"
  where x = image
  by transport_prover

lemma rel_fun_eq_Fun_Rel_rel: "rel_fun = Fun_Rel_rel"
  by (intro ext iffI Dep_Fun_Rel_relI) (auto elim: rel_funE)

lemma image_parametric' [transport_related_intro]:
  "((R \<Rrightarrow> S) \<Rrightarrow> rel_set R \<Rrightarrow> rel_set S) image image"
  using transfer_raw[simplified rel_fun_eq_Fun_Rel_rel Transfer.Rel_def]
  by simp

(*experiment with compositions*)

context
  fixes L1 R1 l1 r1 L R l r
  assumes "(L1 \<equiv>\<^bsub>PER\<^esub> R1) l1 r1"
  defines "L \<equiv> rel_set L1" and "R \<equiv> rel_set R1"
  and "l \<equiv> image l1" and "r \<equiv> image r1"
begin

interpretation transport L R l r .

(*proven for all natural functors*)
lemma transport_per_set: "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r" sorry

end

context
  fixes L1 R1 l1 r1 L R l r
  assumes per1: "(L1 \<equiv>\<^bsub>PER\<^esub> R1) l1 r1"
  and compat:
    "transport_comp.middle_compatible_codom (rel_set R1) typedef_fset.L"
begin

transport_term fempty_param :: "'b fset"
  where x = "{} :: 'a set"
  and L = "transport_comp.L ?L1 ?R1 (?l1 :: 'a set \<Rightarrow> 'b set) ?r1 typedef_fset.L"
  and R = "transport_comp.L typedef_fset.R typedef_fset.L ?r2 ?l2 ?R1"
  apply (rule transport_comp.partial_equivalence_rel_equivalenceI)
    apply (rule transport_per_set[OF per1])
    apply per_prover
    apply (fact compat)
  apply (rule transport_comp.left_relI[where ?y="{}" and ?y'="{}"])
    apply (auto intro!: galois_rel.left_GaloisI in_codomI empty_transfer)
  done

end

definition "set_succ \<equiv> image ((+) (1 :: int))"

lemma set_succ_parametric [transport_in_dom]:
  "(typedef_fset.L \<Rrightarrow> typedef_fset.L) set_succ set_succ"
  unfolding set_succ_def by auto

transport_term fset_succ :: "int fset \<Rightarrow> int fset"
  where x = set_succ
  and L = "typedef_fset.L \<Rrightarrow> typedef_fset.L"
  and R = "typedef_fset.R \<Rrightarrow> typedef_fset.R"
  by transport_prover

lemma Galois_id_hint [unif_hint]:
  "(L :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<equiv> R \<Longrightarrow> r \<equiv> id \<Longrightarrow> E \<equiv> L \<Longrightarrow> (\<^bsub>L\<^esub>\<lessapprox>\<^bsub>R r\<^esub>) \<equiv> E"
  by (simp only: eq_reflection[OF transport_id.left_Galois_eq_left])

transport_term fset_succ' :: "int fset \<Rightarrow> int fset"
  where x = set_succ
  and L = "typedef_fset.L \<Rrightarrow> typedef_fset.L"
  and R = "typedef_fset.R \<Rrightarrow> typedef_fset.R"
  unfold set_succ_def !
  apply (tactic \<open>instantiate_skeleton_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (rule fimage_related')
  apply (assumption)
  defer
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (rule add_parametric)
  apply auto
  oops

lemma pint_middle_compat:
  "transport_comp.middle_compatible_codom (rel_set ((=) :: pint \<Rightarrow> _))
  (=\<^bsub>Collect (finite :: pint set \<Rightarrow> _)\<^esub>)"
  by (intro transport_comp.middle_compatible_codom_if_right1_le_eqI)
  (auto simp: rel_set_eq intro!: transitiveI)

transport_term pint_fset_succ :: "pint fset \<Rightarrow> pint fset"
  where x = "set_succ :: int set \<Rightarrow> int set"
  apply (rule transport_Fun_Rel.partial_equivalence_rel_equivalenceI)
    apply (rule transport_comp.partial_equivalence_rel_equivalenceI)
      apply (rule transport_per_set)
      apply (rule typedef_pint.partial_equivalence_rel_equivalence)
      apply per_prover
      apply (fact pint_middle_compat)
    apply (rule transport_comp.partial_equivalence_rel_equivalenceI)
      apply (rule transport_per_set)
      apply (rule typedef_pint.partial_equivalence_rel_equivalence)
      apply per_prover
      apply (fact pint_middle_compat)
  apply (simp add: transport_def)
  apply (intro Dep_Fun_Rel_relI)
  oops

end


end