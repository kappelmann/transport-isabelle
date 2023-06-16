\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Transport for Set Extensions\<close>
theory Transport_Set_Extension
  imports
    Isabelle_Set.Integers
    Transport_PER
    Transport_Syntax
    Logging.ML_Attributes
begin

paragraph \<open>Summary\<close>
text \<open>Final example from the Transport paper. Transports using different
relations on the same type. Uses the Set-Extension mechanism from Isabelle/Set.
See @{locale set_extension}.\<close>

context
  includes galois_rel_syntax transport_syntax
begin

no_notation Groups.zero_class.zero ("0")

lemma eq_restrict_set_eq_eq_unif_hint [unif_hint]:
  "P \<equiv> mem_of A \<Longrightarrow> ((=\<^bsub>A\<^esub>) :: set \<Rightarrow> _) \<equiv> (=\<^bsub>P\<^esub>)"
  by simp

text \<open>Proof of equivalence is done for all set-extensions in
@{theory Isabelle_Set.Set_Extensions_Transport}.\<close>
declare Int.partial_equivalence_rel_equivalence[per_intro]

definition "RepZ ir i \<equiv> i \<in> \<int> \<and> ir = Int.r i"

lemma int_rep_Galois_eq_RepZ: "(\<^bsub>(=\<^bsub>int_rep\<^esub>)\<^esub>\<lessapprox>\<^bsub>(=\<^bsub>\<int>\<^esub>) Int.r\<^esub>) \<equiv> RepZ"
  unfolding galois_rel.Galois_def RepZ_def by (intro eq_reflection ext) auto

declare int_rep_Galois_eq_RepZ[transport_relator_rewrite, unif_hint]

text \<open>Transport from natural numbers into non-negative integers.\<close>

lemma Int_Rep_nonneg_parametric [transport_in_dom]:
  "((=\<^bsub>\<nat>\<^esub>) \<Rrightarrow> Int.L) Int_Rep_nonneg Int_Rep_nonneg"
  unfolding Int_Rep_nonneg_def int_rep_def by (intro Dep_Fun_Rel_relI) auto

transport_term int_nonneg :: "set \<Rightarrow> set" where
  x = Int_Rep_nonneg and L = "(=\<^bsub>\<nat>\<^esub>) \<Rrightarrow> Int.L" and R = "((=\<^bsub>\<nat>\<^esub>) :: set \<Rightarrow> _) \<Rrightarrow> Int.R"
  by transport_prover

text \<open>Transport from natural numbers into negative integers.\<close>

lemma Int_Rep_neg_parametric [transport_in_dom]:
  "((=\<^bsub>\<nat> \<setminus> {0}\<^esub>) \<Rrightarrow> Int.L) Int_Rep_neg Int_Rep_neg"
  unfolding Int_Rep_neg_def int_rep_def by (intro Dep_Fun_Rel_relI) auto

transport_term int_neg
  where x = Int_Rep_neg and L = "(=\<^bsub>\<nat> \<setminus> {0}\<^esub>) \<Rrightarrow> Int.L"
  and R = "((=\<^bsub>\<nat> \<setminus> {0}\<^esub>) :: set \<Rightarrow> _) \<Rrightarrow> Int.R"
  by transport_prover

text \<open>Transport 0.\<close>

lemma Int_Rep_zero_parametric [transport_in_dom]: "Int_Rep_zero =\<^bsub>int_rep\<^esub> Int_Rep_zero"
  by auto

transport_term int_zero where x = Int_Rep_zero and L = Int.L and R = Int.R
  by transport_prover

text \<open>There is some very limited white-box transport support in the prototype.\<close>
transport_term int_zero' where x = Int_Rep_zero and L = Int.L and R = Int.R
  unfold Int_Rep_zero_def ! (*invoking "!" opens the whitebox goal*)
  (*the whitebox transport prover*)
  by transport_whitebox_prover auto

text \<open>Note the difference in definition between the blackbox and whitebox term\<close>
print_statement int_zero_def int_zero'_def

transport_term lambdatest :: "'a \<Rightarrow> set" where x = "\<lambda>(_ :: 'a). Int_Rep_zero"
  ! (*invoking "!" opens the whitebox goal*)
  (*the whitebox transport prover*)
  by transport_whitebox_prover

transport_term apptest :: "set" where x = "Int_Rep_nonneg 0" !
  by transport_whitebox_prover auto

text \<open>Transport addition\<close>

lemma Int_Rep_add_parametric [transport_in_dom]:
  "(Int.L \<Rrightarrow> Int.L \<Rrightarrow> Int.L) Int_Rep_add Int_Rep_add"
  by (intro Dep_Fun_Rel_relI) fastforce

transport_term int_add where x = Int_Rep_add
  and L = "Int.L \<Rrightarrow> Int.L \<Rrightarrow> Int.L" and R = "Int.R \<Rrightarrow> Int.R \<Rrightarrow> Int.R"
  by transport_prover

text \<open>Transport subtraction\<close>

lemma Int_Rep_sub_parametric [transport_in_dom]:
  "(Int.L \<Rrightarrow> Int.L \<Rrightarrow> Int.L) Int_Rep_sub Int_Rep_sub"
  by (intro Dep_Fun_Rel_relI) fastforce

transport_term int_sub where x = Int_Rep_sub
  and L = "Int.L \<Rrightarrow> Int.L \<Rrightarrow> Int.L" and R = "Int.R \<Rrightarrow> Int.R \<Rrightarrow> Int.R"
  by transport_prover


(* declare[[ML_dattr "fn _ => Logger.set_log_levels First_Order_Unification.logger Logger.ALL"]] *)
(* declare[[show_types]] *)
(* declare[[ML_dattr "fn _ => Logger.set_log_levels Higher_Order_Pattern_Unification.logger Logger.DEBUG"]] *)
(* declare[[ML_dattr "fn _ => Logger.map_logger Higher_Order_Pattern_Unification.logger
  (Logger.set_config_output (K writeln) |> Option.map)"]] *)
transport_term abc :: "set \<Rightarrow> set \<Rightarrow> set" where x = "\<lambda>(_ :: set) y. Int_Rep_add y y" !
  by transport_whitebox_prover

text \<open>Transport a higher-order function\<close>

definition "Int_Rep_if P i x y \<equiv> if P i then x else y"

lemma "Int_Rep_if : (Int_Rep \<Rightarrow> Bool) \<Rightarrow> Int_Rep \<Rightarrow> A \<Rightarrow> A \<Rightarrow> A"
  unfolding Int_Rep_if_def by discharge_types

lemma Int_Rep_if_parametric [transport_in_dom]:
  "((Int.L \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> Int.L \<Rrightarrow> (=)) Int_Rep_if Int_Rep_if"
  unfolding Int_Rep_if_def by (intro Dep_Fun_Rel_relI) auto

transport_term int_if :: "(set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where x = "Int_Rep_if :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and L = "(Int.L \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> Int.L \<Rrightarrow> (=)"
  by transport_prover

lemma Galois_id_hint [unif_hint]:
  "(L :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<equiv> R \<Longrightarrow> r \<equiv> id \<Longrightarrow> E \<equiv> L \<Longrightarrow> (\<^bsub>L\<^esub>\<lessapprox>\<^bsub>R r\<^esub>) \<equiv> E"
  by (simp only: eq_reflection[OF transport_id.left_Galois_eq_left])

context
  fixes P :: "set \<Rightarrow> bool"
  assumes [transport_related_intro]: "(RepZ \<Rrightarrow> (=)) P P"
begin

(*whitebox transport*)
transport_term int_if_app_zero :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where x = "Int_Rep_if P Int_Rep_zero :: 'a \<Rightarrow> 'a \<Rightarrow> 'a" !
  by transport_whitebox_prover

end

definition "app_eq_Int_Rep_zero f x \<equiv> if f x = Int_Rep_zero then True else False"

lemma app_eq_Int_Rep_zero_type:
  "app_eq_Int_Rep_zero : (A \<Rightarrow> Int_Rep) \<Rightarrow> A \<Rightarrow> Bool"
  by discharge_types

lemma app_eq_Int_Rep_parametric [transport_in_dom]:
  "((R \<Rrightarrow> Int.L) \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) app_eq_Int_Rep_zero app_eq_Int_Rep_zero"
  unfolding app_eq_Int_Rep_zero_def
  by (intro Dep_Fun_Rel_relI) (auto elim!: eq_restrictE)

transport_term app_eq_int_zero
  where x = "app_eq_Int_Rep_zero :: (set \<Rightarrow> set) \<Rightarrow> _"
  and L = "(Int.L \<Rrightarrow> Int.L) \<Rrightarrow> Int.L \<Rrightarrow> (\<longleftrightarrow>)"
  and R = "(Int.R \<Rrightarrow> Int.R) \<Rrightarrow> Int.R \<Rrightarrow> (\<longleftrightarrow>)"
  by transport_prover

lemma If_parametric [transport_in_dom, transport_related_intro]: "((\<longleftrightarrow>) \<Rrightarrow> R \<Rrightarrow> R \<Rrightarrow> R) If If"
  by (intro Dep_Fun_Rel_relI) auto

lemma eq_parametric [transport_in_dom, transport_related_intro]:
  (* "((=) \<Rrightarrow> (=) \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)" *)
  (* by (intro Dep_Fun_Rel_relI) auto *)
  "(RepZ \<Rrightarrow> RepZ \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
  sorry

lemma id_parametric [transport_in_dom, transport_related_intro]: "(R \<Rrightarrow> R) id id"
  by (intro Dep_Fun_Rel_relI) auto

context
  fixes f :: "set \<Rightarrow> set"
  assumes [transport_related_intro]: "(RepZ \<Rrightarrow> RepZ) f f"
begin

transport_term whitebox_if_app
  where x = "app_eq_Int_Rep_zero f Int_Rep_zero"
  and L = "(\<longleftrightarrow>)" and R = "(\<longleftrightarrow>)"
  unfold app_eq_Int_Rep_zero_def !
  by transport_whitebox_prover

transport_term int_to_bool'
  where x = "app_eq_Int_Rep_zero :: (set \<Rightarrow> set) \<Rightarrow> _"
  and L = "(Int.L \<Rrightarrow> Int.L) \<Rrightarrow> Int.L \<Rrightarrow> (\<longleftrightarrow>)"
  and R = "(Int.R \<Rrightarrow> Int.R) \<Rrightarrow> Int.R \<Rrightarrow> (\<longleftrightarrow>)"
  unfold app_eq_Int_Rep_zero_def !
  apply (tactic \<open>instantiate_skeleton_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply assumption
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>transport_related_step_tac @{context} 1\<close>)
  apply (resolve_hints refl)
  apply (resolve_hints refl)
  apply (resolve_hints refl)
  apply (fold transport_def)
  apply (transport_relator_rewrite)+
  apply (unfold transport_def)
  apply (resolve_hints refl)
  done

end
end

end