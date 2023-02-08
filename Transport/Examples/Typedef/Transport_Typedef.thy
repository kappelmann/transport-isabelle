theory Transport_Typedef
  imports
    Main
    Transport_Typedef_Base
    Transport_PEE
    Transport_Syntax
begin

context
  includes galois_rel_syntax transport_syntax
begin

typedef pint = "{i :: int. 0 \<le> i}" by auto

interpretation typedef_pint :
  type_definition Rep_pint Abs_pint "{i :: int. 0 \<le> i}"
  by (fact type_definition_pint)


typedef 'a fset = "{s :: 'a set. finite s}" by auto

interpretation typedef_fset :
  type_definition Rep_fset Abs_fset "{s :: 'a set. finite s}"
  by (fact type_definition_fset)


lemma eq_restrict_set_eq_eq_unif_hint [unif_hint]:
  "P \<equiv> \<lambda>x. x \<in> A \<Longrightarrow> ((=\<^bsub>A :: 'a set\<^esub>) :: 'a \<Rightarrow> _) \<equiv> (=\<^bsub>P\<^esub>)"
  by simp

(*could also automatically tagged for every instance in type_definition*)
declare
  typedef_pint.partial_equivalence_equivalence[pee_intro]
  typedef_fset.partial_equivalence_equivalence[pee_intro]


lemma one_parametric [transport_parametric]: "typedef_pint.L 1 1"
  by auto

transport_term pint_one :: "pint" where x = "1 :: int"
  by transport_term_prover


lemma add_parametric [transport_parametric]:
  "(typedef_pint.L \<Rrightarrow> typedef_pint.L \<Rrightarrow> typedef_pint.L) (+) (+)"
  by (intro Dep_Fun_Rel_relI) (auto intro!: eq_restrictI elim!: eq_restrictE)

transport_term pint_add :: "pint \<Rightarrow> pint \<Rightarrow> pint"
  where x = "(+) :: int \<Rightarrow> _"
  by transport_term_prover


lemma empty_parametric [transport_parametric]: "typedef_fset.L {} {}"
  by auto

transport_term fempty :: "'a fset" where x = "{} :: 'a set"
  by transport_term_prover


lemma insert_parametric [transport_parametric]:
  "((=) \<Rrightarrow> typedef_fset.L \<Rrightarrow> typedef_fset.L) insert insert"
  by auto

transport_term finsert :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  where x = insert
  and L = "((=) \<Rrightarrow> typedef_fset.L \<Rrightarrow> typedef_fset.L)"
  and R = "((=) \<Rrightarrow> typedef_fset.R \<Rrightarrow> typedef_fset.R)"
  by transport_term_prover

context
  notes refl[transport_related_intro]
begin

transport_term insert_add_int_fset_whitebox :: "int fset"
  where x = "insert (1 + (1 :: int)) {}" !
  by transport_related_prover

lemma empty_parametric' [transport_related_intro]: "(rel_set R) {} {}"
  by (intro Dep_Fun_Rel_relI rel_setI) (auto dest: rel_setD1 rel_setD2)

lemma insert_parametric' [transport_related_intro]:
  "(R \<Rrightarrow> rel_set R \<Rrightarrow> rel_set R) insert insert"
  by (intro Dep_Fun_Rel_relI rel_setI) (auto dest: rel_setD1 rel_setD2)

(*proven for all natural functors*)
lemma Galois_set_hint [unif_hint]:
  "L \<equiv> rel_set (L1 :: 'a \<Rightarrow> 'a \<Rightarrow> bool)
  \<Longrightarrow> R \<equiv> rel_set (R1 :: 'b \<Rightarrow> 'b \<Rightarrow> bool) \<Longrightarrow> r \<equiv> image r1 \<Longrightarrow> S \<equiv> (\<^bsub>L1\<^esub>\<lessapprox>\<^bsub>R1 r1\<^esub>)
  \<Longrightarrow> (\<^bsub>L\<^esub>\<lessapprox>\<^bsub>R r\<^esub>) \<equiv> rel_set S"
  sorry

transport_term insert_add_pint_set_whitebox :: "pint set"
  where x = "insert (1 + (1 :: int)) {}" !
  by transport_related_prover

print_statement insert_add_int_fset_whitebox_def insert_add_pint_set_whitebox_def

lemma rel_fun_eq_Fun_Rel_rel: "rel_fun = Fun_Rel_rel"
  by (intro ext iffI Dep_Fun_Rel_relI) (auto elim: rel_funE)

transport_term insert_add_pint_fset_whitebox :: "pint fset"
  where x = "insert (1 + (1 :: int)) {}" !
  apply (tactic \<open>any_unify_hints_resolve_tac @{context} [@{thm Fun_Rel_relD}] 1\<close>)+
  defer
  apply (tactic \<open>any_unify_hints_resolve_tac @{context} [@{thm Fun_Rel_relD}] 1\<close>)+
  apply (tactic \<open>any_unify_hints_resolve_tac @{context} [@{thm pint_add_related'}] 1\<close>)
  apply (tactic \<open>any_unify_hints_resolve_tac @{context} [@{thm pint_one_related'}] 1\<close>)
  apply (tactic \<open>any_unify_hints_resolve_tac @{context} [@{thm pint_one_related'}] 1\<close>)
  oops

end

lemma image_parametric [transport_parametric]:
  "(((=) \<Rrightarrow> (=)) \<Rrightarrow> typedef_fset.L \<Rrightarrow> typedef_fset.L) image image"
  by (intro Dep_Fun_Rel_relI) auto

transport_term fimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset"
  where x = image
  by transport_term_prover

lemma image_parametric' [transport_related_intro]:
  "((R \<Rrightarrow> S) \<Rrightarrow> rel_set R \<Rrightarrow> rel_set S) image image"
  using transfer_raw[simplified rel_fun_eq_Fun_Rel_rel Transfer.Rel_def]
  by simp

(* lemma insert_union: "(insert a B) \<union> C = insert a (B \<union> C)"
  by auto *)

(* lemma eq_rel: "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
  using Rep_fset_inject
  by (intro Dep_Fun_Rel_relI) (auto elim!: galois_rel.GaloisE eq_restrictE) *)

(* lemma finsert_funion: "funion (finsert a B) C = finsert a (funion B C)"
proof -
  "(\<longleftrightarrow>) ?target ?goal"
  have "a = a" by auto
  have "Rep_fset B \<^bsub>L\<^esub>\<lessapprox> B"
    by (fact typedef_fset.Galois_Rep_self)
  have "insert a (Rep_fset B) \<^bsub>L\<^esub>\<lessapprox> finsert a B"
   by (fact Dep_Fun_Rel_relD[OF
        Dep_Fun_Rel_relD[OF finsert_related' \<open>a = a\<close>]
        \<open>Rep_fset B \<^bsub>L\<^esub>\<lessapprox> B\<close>
    ])
  have "Rep_fset C \<^bsub>L\<^esub>\<lessapprox> C"
    by (fact typedef_fset.Galois_Rep_self)
  have "union (Rep_fset B) (Rep_fset C) \<^bsub>L\<^esub>\<lessapprox> funion B C"
    by (fact Dep_Fun_Rel_relD[OF
        Dep_Fun_Rel_relD[OF funion_related' \<open>Rep_fset B \<^bsub>L\<^esub>\<lessapprox> B\<close>]
        \<open>Rep_fset C \<^bsub>L\<^esub>\<lessapprox> C\<close>
    ])
  have "funion (finsert a B) C = finsert a (funion B C)
    \<longleftrightarrow>
    union (insert a (Rep_fset B)) (Rep_fset C)
      = insert a (union (Rep_fset B) (Rep_fset C))"
    sorry
  have "union (insert a (Rep_fset B)) (Rep_fset C)
    = insert a (union (Rep_fset B) (Rep_fset C))"
    using insert_union by simp
  show ?thesis sorry
qed *)



(*experiment with compositions*)

context
  fixes L1 R1 l1 r1 L R l r
  assumes "(L1 \<equiv>\<^bsub>PER\<^esub> R1) l1 r1"
  defines "L \<equiv> rel_set L1" and "R \<equiv> rel_set R1"
  and "l \<equiv> image l1" and "r \<equiv> image r1"
begin

interpretation transport L R l r .

(*proven for all natural functors*)
lemma transport_pee_set: "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r" sorry

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
  apply (rule transport_comp.partial_equivalence_equivalenceI)
    apply (rule transport_pee_set[OF per1])
    apply pee_prover
    apply (fact compat)
  apply (rule transport_comp.left_relI[where ?y="{}" and ?y'="{}"])
    apply (auto intro!: galois_rel.GaloisI in_codomI empty_transfer)
  done

end

definition "set_succ \<equiv> image ((+) (1 :: int))"

lemma set_succ_parametric [transport_parametric]:
  "(typedef_fset.L \<Rrightarrow> typedef_fset.L) set_succ set_succ"
  unfolding set_succ_def by auto

transport_term fset_succ :: "int fset \<Rightarrow> int fset"
  where x = set_succ
  and L = "typedef_fset.L \<Rrightarrow> typedef_fset.L"
  and R = "typedef_fset.R \<Rrightarrow> typedef_fset.R"
  by transport_term_prover

(* lemma Galois_id_hint [unif_hint]:
  "(L :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<equiv> R \<Longrightarrow> r \<equiv> id \<Longrightarrow> E \<equiv> L \<Longrightarrow> (\<^bsub>L\<^esub>\<lessapprox>\<^bsub>R r\<^esub>) \<equiv> E"
  by (simp only: eq_reflection[OF transport_id.Galois_eq_left]) *)

lemma Fun_Rel_relD_delay:
  assumes "\<And>x y. R x y \<Longrightarrow> S (f x) (g y)"
  and "T = (R \<Rrightarrow> S)"
  shows "T f g"
  using assms by blast

transport_term fset_succ' :: "int fset \<Rightarrow> int fset"
  where x = set_succ
  and L = "typedef_fset.L \<Rrightarrow> typedef_fset.L"
  and R = "typedef_fset.R \<Rrightarrow> typedef_fset.R"
  unfold set_succ_def !
  apply (tactic \<open>any_unify_hints_resolve_tac @{context} [@{thm Fun_Rel_relD_delay}] 1\<close>)
  (* apply transport_related_prover *)
  apply (tactic \<open>any_unify_hints_resolve_tac @{context} [@{thm Fun_Rel_relD}] 1\<close>)
  apply (tactic \<open>any_unify_hints_resolve_tac @{context} [@{thm Fun_Rel_relD}] 1\<close>)
  apply (tactic \<open>any_unify_hints_resolve_tac @{context} [@{thm fimage_related'}] 1\<close>)
  apply (tactic \<open>any_unify_hints_resolve_tac @{context} [@{thm Fun_Rel_relD}] 1\<close>)
  defer
  apply (tactic \<open>any_unify_hints_resolve_tac @{context} [@{thm refl}] 1\<close>)
  oops

lemma pint_middle_compat:
  "transport_comp.middle_compatible_codom (rel_set ((=) :: pint \<Rightarrow> _))
  (=\<^bsub>Collect (finite :: pint set \<Rightarrow> _)\<^esub>)"
  by (intro transport_comp.middle_compatible_codom_if_right1_le_eqI)
  (auto simp: rel_set_eq intro!: transitiveI)

transport_term pint_fset_succ :: "pint fset \<Rightarrow> pint fset"
  where x = "set_succ :: int set \<Rightarrow> int set"
  apply (rule transport_Fun_Rel.partial_equivalence_equivalenceI)
    apply (rule transport_comp.partial_equivalence_equivalenceI)
      apply (rule transport_pee_set)
      apply (rule typedef_pint.partial_equivalence_equivalence)
      apply pee_prover
      apply (fact pint_middle_compat)
    apply (rule transport_comp.partial_equivalence_equivalenceI)
      apply (rule transport_pee_set)
      apply (rule typedef_pint.partial_equivalence_equivalence)
      apply pee_prover
      apply (fact pint_middle_compat)
  apply (simp add: transport_def)
  apply (intro Dep_Fun_Rel_relI)
  oops

end