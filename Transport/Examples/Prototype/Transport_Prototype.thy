\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transport via Equivalences on PERs (Prototype)\<close>
theory Transport_Prototype
  imports
    Transport_Rel_If
    ML_Unification.ML_Unification_HOL_Setup
    ML_Unification.Unify_Resolve_Tactics
  keywords "trp_term" :: thy_goal_defn
begin

paragraph \<open>Summary\<close>
text \<open>We implement a simple Transport prototype. The prototype is restricted
to work with equivalences on partial equivalence relations.
It is also not forming the compositions of equivalences so far.
The support for dependent function relators is restricted to the form
described in
@{thm transport_Dep_Fun_Rel_no_dep_fun.partial_equivalence_rel_equivalenceI}:
The relations can be dependent, but the functions must be simple.
This is not production ready, but a proof of concept.

The package provides a command @{command trp_term}, which sets up the
required goals to prove a given term. See the examples in this directory for
some use cases and refer to \<^cite>\<open>"transport"\<close> for more details.\<close>

paragraph \<open>Theorem Setups\<close>

context transport
begin

lemma left_Galois_left_if_left_rel_if_partial_equivalence_rel_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<le>\<^bsub>L\<^esub> x'"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x"
  using assms by (intro left_Galois_left_if_left_rel_if_inflationary_on_in_fieldI)
  (blast elim: preorder_equivalence_order_equivalenceE)+

definition "transport_per x y \<equiv> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r \<and> x \<^bsub>L\<^esub>\<lessapprox> y"

text \<open>The choice of @{term "x'"} is arbitrary. All we need is @{term "in_dom (\<le>\<^bsub>L\<^esub>) x"}.\<close>
lemma transport_per_start:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<le>\<^bsub>L\<^esub> x'"
  shows "transport_per x (l x)"
  using assms unfolding transport_per_def
  by (blast intro: left_Galois_left_if_left_rel_if_partial_equivalence_rel_equivalence)

lemma left_Galois_if_transport_per:
  assumes "transport_per x y"
  shows "x \<^bsub>L\<^esub>\<lessapprox> y"
  using assms unfolding transport_per_def by blast

end

context transport_Fun_Rel
begin

text \<open>Simplification of Galois relator for simple function relator.\<close>

corollary left_Galois_eq_Fun_Rel_left_Galois:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))"
proof (intro ext)
  fix f g
  show "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
  proof
    assume "f \<^bsub>L\<^esub>\<lessapprox> g"
    moreover have "g \<le>\<^bsub>R\<^esub> g"
    proof -
      from assms have per: "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
        by (intro partial_equivalence_rel_equivalenceI) auto
      with \<open>f \<^bsub>L\<^esub>\<lessapprox> g\<close> show ?thesis by blast
    qed
    ultimately show "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g" using assms
      by (intro Fun_Rel_left_Galois_if_left_GaloisI)
      (auto elim!: tdfrs.t1.partial_equivalence_rel_equivalenceE
        tdfrs.t1.preorder_equivalence_galois_equivalenceE
        tdfrs.t1.galois_equivalenceE
        intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom)
  next
    assume "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
    with assms have "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub> f g"
      by (subst Fun_Rel_left_Galois_restrict_left_right_eq_Fun_Rel_left_GaloisI) blast+
    with assms show "f \<^bsub>L\<^esub>\<lessapprox> g"
      by (intro left_Galois_if_Fun_Rel_left_GaloisI) blast+
  qed
qed

end

paragraph \<open>General ML setups\<close>

ML_file\<open>transport_util.ML\<close>

ML\<open>
  structure Util = Transport_Util
  val transport_id = "trp"
\<close>

paragraph \<open>Simplifying Definitions\<close>

ML\<open>
  val simp_rhs = Simplifier.rewrite #> Conversion_Util.rhs_conv #> Conversion_Util.thm_conv

  \<comment> \<open>simplifies the generated definition of a transported term\<close>
  fun simp_transported_def ctxt simps y_def =
    let
      val ctxt = ctxt addsimps simps
      val y_def_eta_expanded = Util.equality_eta_expand ctxt "x" y_def
    in apply2 (simp_rhs ctxt) (y_def, y_def_eta_expanded) end
\<close>

text \<open>Definitions used by Transport that need to be folded before a PER proof and unfolded after
success.\<close>
ML\<open>
  structure Transport_Defs = Named_Thms(
    val name = @{binding "transport_def"}
    val description = "Definitions used by Transport"
  )
  val _ = Theory.setup Transport_Defs.setup
\<close>

declare
  transport_Dep_Fun_Rel.transport_defs[transport_def]
  transport_Fun_Rel.transport_defs[transport_def]

paragraph \<open>Unification Setup\<close>

ML\<open>
  @{functor_instance struct_name = Transport_Unification_Combine
    and functor_name = Unification_Combine
    and id = transport_id}
\<close>
local_setup \<open>Transport_Unification_Combine.setup_attribute NONE\<close>
ML\<open>
  @{functor_instance struct_name = Transport_Mixed_Unification
    and functor_name = Mixed_Unification
    and id = transport_id
    and more_args = \<open>structure UC = Transport_Unification_Combine\<close>}
\<close>

ML\<open>
  @{functor_instance struct_name = Transport_Unification_Hints
    and functor_name = Term_Index_Unification_Hints
    and id = transport_id
    and more_args = \<open>
      structure TI = Discrimination_Tree
      val init_args = {
        concl_unifier = SOME Higher_Order_Pattern_Unification.unify,
        normalisers = SOME Transport_Mixed_Unification.norms_first_higherp_first_comb_higher_unify,
        prems_unifier = SOME (Transport_Mixed_Unification.first_higherp_first_comb_higher_unify
          |> Unification_Combinator.norm_unifier Envir_Normalisation.beta_norm_term_unif),
        retrieval = SOME (Term_Index_Unification_Hints_Args.mk_sym_retrieval
          TI.norm_term TI.unifiables),
        hint_preprocessor = SOME (K I)
      }\<close>}
\<close>
local_setup \<open>Transport_Unification_Hints.setup_attribute NONE\<close>
declare [[trp_uhint where hint_preprocessor = \<open>Unification_Hints_Base.obj_logic_hint_preprocessor
  @{thm atomize_eq[symmetric]} (Conv.rewr_conv @{thm eq_eq_True})\<close>]]
declare [[trp_ucombine add = \<open>Transport_Unification_Combine.eunif_data
  (Transport_Unification_Hints.try_hints
  |> Unification_Combinator.norm_unifier
    (#norm_term Transport_Mixed_Unification.norms_first_higherp_first_comb_higher_unify)
  |> K)
  (Transport_Unification_Combine.default_metadata Transport_Unification_Hints.binding)\<close>]]

paragraph \<open>Resolution Setup\<close>

ML\<open>
  \<comment> \<open>resolution with above unifier\<close>
  val any_unify_trp_hints_resolve_tac = Unify_Resolve_Base.unify_resolve_any_tac
    Transport_Mixed_Unification.norms_first_higherp_first_comb_higher_unify
    Transport_Mixed_Unification.first_higherp_first_comb_higher_unify

  fun get_theorems_tac f get_theorems ctxt = f (get_theorems ctxt) ctxt
  val get_theorems_resolve_tac = get_theorems_tac any_unify_trp_hints_resolve_tac
\<close>

method_setup trp_hints_resolve =
  \<open>Attrib.thms >> (SIMPLE_METHOD' oo any_unify_trp_hints_resolve_tac)\<close>
  "Resolution with unification hints for Transport "

paragraph \<open>PER equivalence prover\<close>

text \<open>Introduction rules.\<close>

ML\<open>
  structure PER_Intros = Named_Thms(
    val name = @{binding "per_intro"}
    val description = "Introduction rules for per_prover"
  )
  val _ = Theory.setup PER_Intros.setup
\<close>

declare
  (*dependent case currently disabled by default since they easily make the
    unifier enumerate many undesired instantiations*)
  (* transport_Dep_Fun_Rel.partial_equivalence_rel_equivalenceI[per_intro] *)
  (* transport.rel_if_partial_equivalence_rel_equivalence_if_iff_if_partial_equivalence_rel_equivalenceI[rotated, per_intro]
  transport_Dep_Fun_Rel_no_dep_fun.partial_equivalence_rel_equivalenceI
    [ML_Krattr \<open>Conversion_Util.move_prems_to_front_conv [1] |> Conversion_Util.thm_conv\<close>,
    ML_Krattr \<open>Conversion_Util.move_prems_to_front_conv [2,3] |> Conversion_Util.thm_conv\<close>,
    per_intro] *)
  transport_Fun_Rel.partial_equivalence_rel_equivalenceI[rotated, per_intro]
  transport_eq_id.partial_equivalence_rel_equivalenceI[per_intro]
  transport_eq_restrict_id.partial_equivalence_rel_equivalence[per_intro]

ML\<open>
  fun per_prover_tac ctxt = REPEAT_ALL_NEW (get_theorems_resolve_tac PER_Intros.get ctxt)
\<close>

method_setup per_prover =
  \<open>Scan.succeed (SIMPLE_METHOD' o per_prover_tac)\<close>
  "PER prover for Transport"


paragraph \<open>Domain Prover\<close>

ML\<open>
  structure Transport_in_dom = Named_Thms(
    val name = @{binding "transport_in_dom"}
    val description = "In domain theorems for Transport"
  )
  val _ = Theory.setup Transport_in_dom.setup
\<close>

text \<open>Discharges the @{term "L x x'"} goals by registered lemmas.\<close>
ML\<open>
  fun transport_in_dom_prover_tac ctxt = get_theorems_resolve_tac Transport_in_dom.get ctxt
\<close>

method_setup transport_in_dom_prover =
  \<open>Scan.succeed (SIMPLE_METHOD' o transport_in_dom_prover_tac)\<close>
  "in_dom prover for Transport"


paragraph \<open>Blackbox Prover\<close>

text \<open>First derives the PER equivalence, then looks for registered domain lemmas.\<close>
ML\<open>
  fun unfold_tac thms ctxt = simp_tac (clear_simpset ctxt addsimps thms)
  val unfold_transport_defs_tac = get_theorems_tac unfold_tac Transport_Defs.get

  fun transport_prover ctxt i =
    per_prover_tac ctxt i
    THEN TRY (SOMEGOAL
      (TRY o unfold_transport_defs_tac ctxt
      THEN' transport_in_dom_prover_tac ctxt)
    )
\<close>

method_setup transport_prover =
  \<open>Scan.succeed (SIMPLE_METHOD' o transport_prover)\<close>
  "Blackbox prover for Transport"


paragraph \<open>Whitebox Prover Intro Rules\<close>

ML\<open>
  structure Transport_Related_Intros = Named_Thms(
    val name = @{binding "transport_related_intro"}
    val description = "Introduction rules for Transport whitebox proofs"
  )
  val _ = Theory.setup Transport_Related_Intros.setup
\<close>


paragraph \<open>Relator Rewriter\<close>

text \<open>Rewrite rules to simplify the derived Galois relator.\<close>
ML\<open>
  structure Transport_Relator_Rewrites = Named_Thms(
    val name = @{binding "transport_relator_rewrite"}
    val description = "Rewrite rules for relators used by Transport"
  )
  val _ = Theory.setup Transport_Relator_Rewrites.setup
\<close>

declare
  transport_id.left_Galois_eq_left[transport_relator_rewrite]
  transport_Fun_Rel.left_Galois_eq_Fun_Rel_left_Galois[transport_relator_rewrite]

ML\<open>
  (*simple rewrite tactic for Galois relators*)
  fun per_simp_prover ctxt thm =
    let
      val prems = Thm.cprems_of thm
      val per_prover_tac = per_prover_tac ctxt
      fun prove_prem prem = Goal.prove_internal ctxt [] prem (fn _ => HEADGOAL per_prover_tac)
    in try (map prove_prem) prems |> Option.map (curry (op OF) thm) end
  fun transport_relator_rewrite ctxt thm =
    let
      val transport_defs = Transport_Defs.get ctxt
      val transport_relator_rewrites = Transport_Relator_Rewrites.get ctxt
      val ctxt = (clear_simpset ctxt) addsimps transport_relator_rewrites
    in
      Local_Defs.fold ctxt transport_defs thm
      |> Raw_Simplifier.rewrite_thm (false, false, false) per_simp_prover ctxt
    end
  fun transport_relator_rewrite_tac ctxt =
    EqSubst.eqsubst_tac ctxt [0] (Transport_Relator_Rewrites.get ctxt)
    THEN_ALL_NEW TRY o SOLVED' (per_prover_tac ctxt)
\<close>

method_setup transport_relator_rewrite =
  \<open>Scan.succeed (SIMPLE_METHOD' o transport_relator_rewrite_tac)\<close>
  "Rewrite Transport relator"


paragraph \<open>The trp\_term command\<close>

text \<open>Parsing\<close>

ML\<open>
  @{parse_entries (struct) PA [L, R, x, y]}
  val parse_cmd_entries =
    let
      val parse_value = PA.parse_entry Parse.term Parse.term Parse.term Parse.term
      val parse_entry = Parse_Key_Value.parse_entry PA.parse_key Parse_Util.eq parse_value
    in PA.parse_entries_required Parse.and_list1 [PA.key PA.x] parse_entry (PA.empty_entries ()) end
\<close>

ML\<open>
  (*some utilities to destruct terms*)
  val transport_per_start_thm = @{thm "transport.transport_per_start"}
  val related_if_transport_per_thm = @{thm "transport.left_Galois_if_transport_per"}
  fun dest_transport_per \<^Const_>\<open>transport.transport_per S T for L R l r x y\<close> =
    ((S, T), (L, R, l, r, x, y))
  val dest_transport_per_y = dest_transport_per #> (fn (_, (_, _, _, _, _, y)) => y)

  fun mk_hom_Galois Ta Tb L R r x y =
    \<^Const>\<open>galois_rel.Galois Ta Ta Tb Tb for L R r x y\<close>
  fun dest_hom_Galois \<^Const_>\<open>galois_rel.Galois Ta _ Tb _ for L R r x y\<close> =
    ((Ta, Tb), (L, R, r, x, y))
  val dest_hom_Galois_y = dest_hom_Galois #> (fn (_, (_, _, _, _, y)) => y)

  (*bindings for generated theorems and definitions*)
  val binding_transport_per = \<^binding>\<open>transport_per\<close>
  val binding_per = \<^binding>\<open>per\<close>
  val binding_in_dom = \<^binding>\<open>in_dom\<close>
  val binding_related = \<^binding>\<open>related\<close>
  val binding_related_rewritten = \<^binding>\<open>related'\<close>
  val binding_def_simplified = \<^binding>\<open>eq\<close>
  val binding_def_eta_expanded_simplified = \<^binding>\<open>app_eq\<close>

  fun note_facts (binding, mixfix) ctxt related_thm y binding_thms_attribs =
    let
      val ((_, (_, y_def)), ctxt) = Util.create_local_theory_def (binding, mixfix) [] y ctxt
      (*create simplified definition theorems*)
      val transport_defs = Transport_Defs.get ctxt
      val (y_def_simplified, y_def_eta_expanded_simplified) =
        simp_transported_def ctxt transport_defs y_def
      (*create relatedness theorems*)
      val related_thm_rewritten = transport_relator_rewrite ctxt related_thm
      fun prepare_fact (suffix, thm, attribs) =
        let
          val binding = (Util.add_suffix binding suffix, [])
          val ctxt = (clear_simpset ctxt) addsimps transport_defs
          val folded_thm =
            (*fold definition of transported term*)
            Local_Defs.fold ctxt [y_def] thm
            (*simplify other transport definitions in theorem*)
            |> (Simplifier.rewrite ctxt |> Conversion_Util.thm_conv)
          val thm_attribs = ([folded_thm], attribs)
        in (binding, [thm_attribs]) end
      val facts = map prepare_fact ([
          (binding_related, related_thm, []),
          (binding_related_rewritten, related_thm_rewritten,
            [Util.attrib_to_src (Binding.pos_of binding) Transport_Related_Intros.add]),
          (binding_def_simplified, y_def_simplified, []),
          (binding_def_eta_expanded_simplified, y_def_eta_expanded_simplified, [])
        ] @ binding_thms_attribs)
    in Local_Theory.notes facts ctxt |> snd end

  (*black-box transport as described in the Transport paper*)
  fun after_qed_blackbox (binding, mixfix) [thms as [per_thm, in_dom_thm]] ctxt =
    let
      val transport_per_thm = List.foldl (op INCR_COMP) transport_per_start_thm thms
      (*fix possibly occurring meta type variables*)
      val ((_, [transport_per_thm]), ctxt) = Variable.importT [transport_per_thm] ctxt
      val y = Util.real_thm_concl transport_per_thm |> dest_transport_per_y

      val related_thm = transport_per_thm INCR_COMP related_if_transport_per_thm
      val binding_thms = [
          (binding_transport_per, transport_per_thm, []),
          (binding_per, per_thm, []),
          (binding_in_dom, in_dom_thm,
            [Util.attrib_to_src (Binding.pos_of binding) Transport_in_dom.add])
        ]
    in note_facts (binding, mixfix) ctxt related_thm y binding_thms end

  (*experimental white-box transport support*)
  fun after_qed_whitebox (binding, mixfix) [[related_thm]] ctxt =
    let
      (*fix possibly occurring meta type variables*)
      val ((_, [related_thm]), ctxt) = Variable.importT [related_thm] ctxt
      val y = Util.real_thm_concl related_thm |> dest_hom_Galois_y
    in note_facts (binding, mixfix) ctxt related_thm y [] end

  fun setup_goals_blackbox ctxt (L, R, cx) maxidx =
    let
      (*check*)
      val [cL, cR] = Syntax.check_terms ctxt [L, R] |> map (Thm.cterm_of ctxt)
      (*instantiate theorem*)
      val transport_per_start_thm = Thm.incr_indexes (maxidx + 1) transport_per_start_thm
      val args = [SOME cL, SOME cR, NONE, NONE, SOME cx]
      val transport_per_start_thm = Drule.infer_instantiate' ctxt args transport_per_start_thm
      val transport_defs = Transport_Defs.get ctxt
      val goals = Local_Defs.fold ctxt transport_defs transport_per_start_thm
        |> Thm.prems_of
        |> map (rpair [])
    in goals end

  fun setup_goals_whitebox ctxt (yT, L, R, cx, y) maxidx =
    let
      val (r, _) = Term_Util.fresh_var "r" dummyT maxidx
      (*check*)
      val Galois = mk_hom_Galois (Thm.typ_of_cterm cx) yT L R r (Thm.term_of cx) y
        |> Syntax.check_term ctxt
      val goal = Util.mk_judgement Galois |> rpair []
    in [goal] end

  fun setup_proof ((((binding, opt_yT, mixfix), params), unfolds), whitebox) lthy =
    let
      val ctxt = Util.set_proof_mode_schematic lthy
      (*type of transported term*)
      val yT = Option.map (Syntax.read_typ ctxt) opt_yT |> the_default dummyT
      (*theorems to unfold*)
      val unfolds = map (Proof_Context.get_fact ctxt o fst) unfolds |> flat
      (*term to transport*)
      val cx =
        (**read term**)
        Syntax.read_term ctxt (PA.get_x params) |> Thm.cterm_of ctxt
        (**unfold passed theorems**)
        |> Drule.cterm_rule (Local_Defs.unfold ctxt unfolds)
      (*transport relations and transport term goal*)
      val ([L, R, y], maxidx) =
        let
          (**configuration**)
          val opts = [PA.get_L_safe params, PA.get_R_safe params, PA.get_y_safe params]
          val opts_default_names = ["L", "R", "y"]
          val opts_constraints =
            [Util.mk_hom_rel_type (Thm.typ_of_cterm cx), Util.mk_hom_rel_type yT, yT]
            |> map Type.constraint
          (**parse**)
          val opts = map (Syntax.parse_term ctxt |> Option.map) opts
          val params_maxidx = Util.list_max (the_default ~1 o Option.map Term.maxidx_of_term)
            (Thm.maxidx_of_cterm cx) opts
          fun create_var (NONE, n) maxidx =
                Term_Util.fresh_var n dummyT params_maxidx ||> Integer.max maxidx
            | create_var (SOME t, _) created = (t, created)
          val (ts, maxidx) =
            fold_map create_var (opts ~~ opts_default_names) params_maxidx
            |>> map2 I opts_constraints
        in (ts, maxidx) end
      (*initialise goals and callback*)
      val (goals, after_qed) = if whitebox
        then (setup_goals_whitebox ctxt (yT, L, R, cx, y) maxidx, after_qed_whitebox)
        (*TODO: consider y in blackbox proofs*)
        else (setup_goals_blackbox ctxt (L, R, cx) maxidx, after_qed_blackbox)
    in
      Proof.theorem NONE (after_qed (binding, mixfix)) [goals] ctxt
      |> Proof.refine_singleton Util.split_conjunctions
    end

  val parse_strings =
    (*binding for transported term*)
    Parse_Spec.constdecl
    (*other params*)
    -- parse_cmd_entries
    (*optionally pass unfold theorems in case of white-box transports*)
    -- Scan.optional (Parse.reserved "unfold" |-- Parse.thms1) []
    (*use a bang "!" to start white-box transport mode (experimental)*)
    -- Parse.opt_bang

  val _ =
    Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>trp_term\<close>
      "transport of definition" (parse_strings >> setup_proof)
\<close>

paragraph \<open>Experimental White-Box Prover\<close>

lemmas related_Fun_Rel_combI = Dep_Fun_Rel_relD[where ?S="\<lambda>_ _. S" for S, rotated]
lemma related_Fun_Rel_lambdaI:
  assumes "\<And>x y. R x y \<Longrightarrow> S (f x) (g y)"
  and "T = (R \<Rrightarrow> S)"
  shows "T f g"
  using assms by blast

ML\<open>
  val any_match_resolve_related_tac =
    let fun unif binders = Higher_Ordern_Pattern_First_Decomp_Unification.e_match
      Unification_Util.match_types unif Unification_Combinator.fail_unify binders
    in
      Unify_Resolve_Base.unify_resolve_any_tac
        Higher_Ordern_Pattern_First_Decomp_Unification.norms_match unif
    end

  val related_comb_tac = any_match_resolve_related_tac @{thms related_Fun_Rel_combI}
  val related_lambda_tac = any_match_resolve_related_tac @{thms related_Fun_Rel_lambdaI}
  val related_tac = any_unify_trp_hints_resolve_tac
  val related_assume_tac = assume_tac

  fun mk_transport_related_tac cc_comb cc_lambda ctxt =
    let
      val transport_related_intros = Transport_Related_Intros.get ctxt
      val related_tac = related_tac transport_related_intros ctxt
      val comb_tac = related_comb_tac ctxt
      val lambda_tac = related_lambda_tac ctxt
      val assume_tac = related_assume_tac ctxt
    in
      Tactic_Util.CONCAT' [
        related_tac,
        cc_comb comb_tac,
        cc_lambda lambda_tac,
        assume_tac
      ]
    end
  val transport_related_step_tac =
    let fun cc_comb tac i = tac i
      THEN prefer_tac i
      THEN prefer_tac (i + 1)
    in mk_transport_related_tac cc_comb I end
  fun transport_related_tac ctxt =
    let
      fun transport_related_tac cc =
        let
          fun cc_comb tac = tac THEN_ALL_NEW TRY o cc
          fun cc_lambda tac = tac THEN' TRY o cc
        in mk_transport_related_tac cc_comb cc_lambda ctxt end
      fun fix tac i thm = tac (fix tac) i thm
    in fix transport_related_tac end
\<close>

method_setup transport_related_prover =
  \<open>Scan.succeed (SIMPLE_METHOD' o transport_related_tac)\<close>
  "Relatedness prover for Transport"

ML\<open>
  fun instantiate_tac name ct ctxt =
    PRIMITIVE (Drule.infer_instantiate_types ctxt [((name, Thm.typ_of_cterm ct), ct)])
    |> CHANGED

  val map_dummyT = Term.map_types (K dummyT)

  fun mk_term_skeleton maxidx t =
    let
      val consts = Term.add_consts t []
      val (vars, _) = fold_map (uncurry Term_Util.fresh_var o apfst Long_Name.base_name) consts maxidx
      val t' = Term.subst_atomic (map2 (pair o Const) consts vars) t
    in t' end

  fun instantiate_skeleton_tac ctxt =
    let fun tac ct =
      let
        val (x, y) = Util.cdest_judgement ct |> Thm.dest_binop
        val default_sort = Proof_Context.default_sort ctxt
        val skeleton =
          mk_term_skeleton (Thm.maxidx_of_cterm ct) (Thm.term_of x)
          |> map_dummyT
          |> Type.constraint (Thm.typ_of_cterm y)
          |> Syntax.check_term (Util.set_proof_mode_pattern ctxt)
          (*add sort constraints for type variables*)
          |> Term.map_types (Term.map_atyps (map_type_tvar (fn (n, _) => TVar (n, default_sort n))))
          |> Thm.cterm_of ctxt
      in instantiate_tac (Thm.term_of y |> dest_Var |> fst) skeleton ctxt end
    in Tactic_Util.CSUBGOAL_DATA I (K o tac) end
\<close>

ML\<open>
  fun transport_whitebox_tac ctxt =
    instantiate_skeleton_tac ctxt
    THEN' transport_related_tac ctxt
    THEN_ALL_NEW (
      TRY o REPEAT1 o transport_relator_rewrite_tac ctxt
      THEN' TRY o any_unify_trp_hints_resolve_tac @{thms refl} ctxt
    )
\<close>

method_setup transport_whitebox_prover =
  \<open>Scan.succeed (SIMPLE_METHOD' o transport_whitebox_tac)\<close>
  "Whitebox prover for Transport"


end
