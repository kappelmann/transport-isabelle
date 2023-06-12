\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transport via Equivalences on PERs\<close>
theory Transport_PER
  imports
    Transport.Transport
    Transport_Rel_If
    "HOL-Eisbach.Eisbach"
    ML_Unification.ML_Unification
    ML_Unification.ML_Unification_Resolution
  keywords "transport_term" :: thy_goal_defn
begin

paragraph \<open>Summary\<close>
text \<open>We implement a simple Transport prototype. The prototype is restricted
to work with equivalences on partial equivalence relations.
It is also not forming the compositions of equivalences so far.
The support for dependent function relators is restricted to the form
described in
@{thm transport_Dep_Fun_Rel_no_dep_fun.partial_equivalence_rel_equivalenceI}.
The relations can be dependent, but the functions must be simple.
This is not production ready, but a proof of concept.

The package provides a command @{command "transport_term"}, which sets up the
required goals to prove a given term. See the examples in this directory for
some use cases and refer to the paper
"Transport via Partial Galois Connections and Equivalences" by Kevin Kappelmann
for more details.\<close>

context transport
begin

lemma left_Galois_left_if_left_rel_if_partial_equivalence_rel_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<le>\<^bsub>L\<^esub> x"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x"
  using assms by (intro left_Galois_left_if_left_rel_if_inflationary_on_in_fieldI)
  (blast elim: preorder_equivalence_order_equivalenceE)+

definition "transport_per x y \<equiv> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r \<and> x \<^bsub>L\<^esub>\<lessapprox> y"

text \<open>The choice of @{term "x \<le>\<^bsub>L\<^esub> x"} is arbitrary. All we need is @{term "in_dom (\<le>\<^bsub>L\<^esub>) x"}.\<close>
lemma transport_per_start:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<le>\<^bsub>L\<^esub> x"
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

ML_file\<open>util.ML\<close>
ML_file\<open>parse_util.ML\<close>

ML\<open>
  structure Util = Transport_Util
  structure CUtil = Conversion_Util
  structure UUtil = Unification_Util
  structure PUtil = Transport_Parse_Util
\<close>

ML\<open>
  (*simplifies the generated definition of a transported term*)
  fun simp_def ctxt simps y_def =
    let
      val ctxt = ctxt addsimps simps
      val rhs_simp_conv = Simplifier.rewrite ctxt |> CUtil.rhs_conv |> CUtil.thm_conv
      val y_def_simplified = rhs_simp_conv y_def

      val y_def_eta_expanded = Util.equality_eta_expand ctxt "x" y_def
      val y_def_eta_expanded_simplified = rhs_simp_conv y_def_eta_expanded
    in (y_def_simplified, y_def_eta_expanded_simplified) end
\<close>

text \<open>Definitions used by Transport that need to be folded before a proof and
unfolded after success.\<close>
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

ML\<open>
  (*first-order unification with higher-order pattern unification with hints as a fallback*)
  val norm_thm_beta_eta =
    UUtil.norm_thm_beta_eta UUtil.norm_type_unif UUtil.norm_term_unif
  fun unify_hints ctxt =
    let
      val unify_types = UUtil.unify_types
      val hints = Unification_Hints.gen_hint_list ctxt
      val unif_hints = Higher_Order_Pattern_Unification.unify
      val norm_thm_unif = norm_thm_beta_eta
      fun ho_unify ctxt = Higher_Order_Pattern_Unification.e_unify
        unify_types (Unification_Hints.try_hints unif_hints norm_thm_unif ho_unify hints)
        ctxt
      val unify = First_Order_Unification.e_unify unify_types ho_unify
    in unify ctxt end

  (*resoluton with above unifier*)
  val any_unify_hints_resolve_tac = Unify_Resolve.any_unify_resolve_tac
    norm_thm_beta_eta unify_hints
\<close>

text \<open>Introduction rules for the PER equivalence prover.\<close>
ML\<open>
  structure PER_Intros = Named_Thms(
    val name = @{binding "per_intro"}
    val description = "Introduction rules for per_prover"
  )
  val _ = Theory.setup PER_Intros.setup
\<close>

declare
  (*completely dependent case not supported as of now*)
  (* transport_Dep_Fun_Rel.partial_equivalence_rel_equivalenceI[per_intro] *)
  transport_Dep_Fun_Rel_no_dep_fun.partial_equivalence_rel_equivalenceI[per_intro]
  (*transport.rel_if_partial_equivalence_rel_equivalence_if_iff_if_partial_equivalence_rel_equivalenceI[per_intro]*)
  transport_Fun_Rel.partial_equivalence_rel_equivalenceI[per_intro]
  transport_eq_id.partial_equivalence_rel_equivalenceI[per_intro]
  transport_eq_restrict_id.partial_equivalence_rel_equivalence[per_intro]

ML\<open>
  fun per_prover_tac ctxt =
    let
      val per_intros = PER_Intros.get ctxt
      val resolve_tac = any_unify_hints_resolve_tac
    in REPEAT1 o resolve_tac per_intros ctxt end
\<close>

method_setup per_prover =
  \<open>Scan.succeed (SIMPLE_METHOD o HEADGOAL o per_prover_tac)\<close>
  "PER prover for Transport"

ML\<open>
  structure Transport_Parametrics = Named_Thms(
    val name = @{binding "transport_parametric"}
    val description = "Parametricity theorems for Transport"
  )
  val _ = Theory.setup Transport_Parametrics.setup
\<close>

text \<open>Discharges the @{term "L x x"} goals by registered lemmas.\<close>
ML\<open>
  fun parametricity_prover_tac ctxt =
    let
      val transport_defs = Transport_Defs.get ctxt
      val transport_parametric = Transport_Parametrics.get ctxt
      val resolve_tac = any_unify_hints_resolve_tac
      val ctxt = clear_simpset ctxt addsimps transport_defs
    in
      full_simp_tac ctxt
      THEN' resolve_tac transport_parametric ctxt
    end
\<close>

method_setup parametricity_prover =
  \<open>Scan.succeed (SIMPLE_METHOD o FIRSTGOAL o parametricity_prover_tac)\<close>
  "parametricity prover for Transport"


text \<open>First derive the PER equivalence, then look for registered
parametricity lemmas.\<close>
method transport_term_prover = per_prover, parametricity_prover?

ML\<open>
  structure Transport_Related_Intros = Named_Thms(
    val name = @{binding "transport_related_intro"}
    val description = "Introduction rules for Transport whitebox proofs"
  )
  val _ = Theory.setup Transport_Related_Intros.setup
\<close>

text \<open>Rewrite rules to simplify the derived Galois relator.\<close>
ML\<open>
  structure Transport_Relator_Rewrites = Named_Thms(
    val name = @{binding "transport_relator_rewrite"}
    val description = "Rewrite rules for relators used by Transport"
  )
  val _ = Theory.setup Transport_Relator_Rewrites.setup
\<close>

declare
  transport_Fun_Rel.left_Galois_eq_Fun_Rel_left_Galois[transport_relator_rewrite]
  transport_id.left_Galois_eq_left[transport_relator_rewrite]

ML\<open>
  (*simple rewrite tactic for Galois relators*)
  fun per_simp_prover ctxt thm =
    let
      val prems = Thm.cprems_of thm
      val per_prover_tac = per_prover_tac ctxt
      fun prove_prem prem =
        Goal.prove_internal ctxt [] prem (fn _ => HEADGOAL per_prover_tac)
    in
      try (map prove_prem) prems
      |> Option.map (curry (op OF) thm)
    end
  fun transport_relator_rewrite ctxt thm =
    let
      val transport_defs = Transport_Defs.get ctxt
      val thm = Local_Defs.fold ctxt transport_defs thm
      val transport_relator_rewrites = Transport_Relator_Rewrites.get ctxt
      val ctxt = (clear_simpset ctxt) addsimps transport_relator_rewrites
    in
      Raw_Simplifier.rewrite_thm (false, false, false) per_simp_prover ctxt thm
    end
\<close>

text \<open>Parsing setup\<close>

ML\<open>
  type cmd_params =
    { L : string option, R : string option, x : string option, y : string option }
  val empty_cmd_params = { L = NONE, R = NONE, x = NONE, y = NONE }
local
  datatype cmd_param_names = L | R | x | y
  val cmd_param_names = [L, R, x, y]
  val required_cmd_param_names = [x]
  fun cmd_param_name_to_string L = "L"
    | cmd_param_name_to_string R = "R"
    | cmd_param_name_to_string x = "x"
    | cmd_param_name_to_string y = "y"
  val cmd_param_name_strings = map cmd_param_name_to_string cmd_param_names
  fun cmd_param_name_from_string "L" = L
    | cmd_param_name_from_string "R" = R
    | cmd_param_name_from_string "x" = x
    | cmd_param_name_from_string "y" = y
    | cmd_param_name_from_string n = Scan.fail ("Parameter " ^ n ^ " not registered")
in
  fun set_cmd_param (L, s) ({R = optR, x = optx, y = opty,...} : cmd_params) =
      {L = SOME s, R = optR, x = optx, y = opty}
    | set_cmd_param (R, s) {L = optL, x = optx, y = opty,...} =
      {L = optL, R = SOME s, x = optx, y = opty}
    | set_cmd_param (x, s) {L = optL, R = optR, y = opty,...} =
      {L = optL, R = optR, x = SOME s, y = opty}
    | set_cmd_param (y, s) {L = optL, R = optR, x = optx,...} =
      {L = optL, R = optR, x = optx, y = SOME s}
  val cmd_params_parser =
    let
      val name_parser =
        PUtil.name_parser cmd_param_name_strings cmd_param_name_from_string
      val entry_parser = PUtil.entry_parser name_parser PUtil.eq_parser Parse.term
    in
      PUtil.required_entries_parser entry_parser cmd_param_name_to_string
        required_cmd_param_names
    end
end
\<close>

text \<open>The transport_term command\<close>

ML\<open>
  (*some utilities to destruct terms*)
  val transport_per_start_thm = @{thm "transport.transport_per_start"}
  val related_if_transport_per_thm = @{thm "transport.left_Galois_if_transport_per"}
  fun dest_transport_per \<^Const_>\<open>transport.transport_per S T for L R l r x y\<close>
    = ((S, T), (L, R, l, r, x, y))
  val dest_transport_per_y = dest_transport_per #> (fn (_, (_, _, _, _, _, y)) => y)

  fun mk_hom_Galois Ta Tb L R r x y =
    \<^Const>\<open>galois_rel.Galois Ta Ta Tb Tb for L R r x y\<close>
  fun dest_hom_Galois \<^Const_>\<open>galois_rel.Galois Ta _ Tb _ for L R r x y\<close>
    = ((Ta, Tb), (L, R, r, x, y))
  val dest_hom_Galois_y = dest_hom_Galois #> (fn (_, (_, _, _, _, y)) => y)

  (*bindings for generated theorems and definitions*)
  val binding_transport_per = \<^binding>\<open>transport_per\<close>
  val binding_per = \<^binding>\<open>per\<close>
  val binding_parametric = \<^binding>\<open>parametric\<close>
  val binding_related = \<^binding>\<open>related\<close>
  val binding_related_rewritten = \<^binding>\<open>related'\<close>
  val binding_def_simplified = \<^binding>\<open>eq\<close>
  val binding_def_eta_expanded_simplified = \<^binding>\<open>app_eq\<close>

  fun note_facts (binding, mixfix) ctxt related_thm y binding_thms_attribs =
    let
      val ((_, (_, y_def)), ctxt) =
        Util.create_local_theory_def (binding, mixfix) [] y ctxt
      (*create simplified definition theorems*)
      val def_simps = Transport_Defs.get ctxt
      val (y_def_simplified, y_def_eta_expanded_simplified) =
        simp_def ctxt def_simps y_def
      (*create relatedness theorems*)
      val related_thm_rewritten = transport_relator_rewrite ctxt related_thm
      fun prepare_fact (suffix, thm, attribs) =
        let
          val binding = (Util.add_suffix binding suffix, [])
          val ctxt = (clear_simpset ctxt) addsimps def_simps
          val folded_thm =
            (*fold definition of transported term*)
            Local_Defs.fold ctxt [y_def] thm
            (*simplify other transport definitions in theorem*)
            |> (Simplifier.rewrite ctxt |> CUtil.thm_conv)
          val thm_attribs = ([folded_thm], attribs)
        in (binding, [thm_attribs]) end
      val facts = map prepare_fact ([
          (binding_related, related_thm, []),
          (binding_related_rewritten, related_thm_rewritten,
            [Util.attrib_to_src Transport_Related_Intros.add]),
          (binding_def_simplified, y_def_simplified, []),
          (binding_def_eta_expanded_simplified, y_def_eta_expanded_simplified, [])
        ] @ binding_thms_attribs)
    in Local_Theory.notes facts ctxt |> snd end

  (*black-box transport as described in the Transport paper*)
  fun after_qed_blackbox (binding, mixfix) [thms as [per_thm, parametricity_thm]] ctxt =
    let
      val transport_per_thm = List.foldl (op INCR_COMP) transport_per_start_thm thms
      (*fix possibly occurring meta type variables*)
      val ((_, [transport_per_thm]), ctxt) = Variable.importT [transport_per_thm] ctxt
      val y = Util.real_thm_concl transport_per_thm |> dest_transport_per_y

      val related_thm = transport_per_thm INCR_COMP related_if_transport_per_thm
      val binding_thms = [
          (binding_transport_per, transport_per_thm, []),
          (binding_per, per_thm, []),
          (binding_parametric, parametricity_thm,
            [Util.attrib_to_src Transport_Parametrics.add])
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
      val transport_per_start_thm =
        Thm.incr_indexes (maxidx + 1) transport_per_start_thm
      val args = [SOME cL, SOME cR, NONE, NONE, SOME cx]
      val transport_per_start_thm =
        Drule.infer_instantiate' ctxt args transport_per_start_thm
      val transport_defs = Transport_Defs.get ctxt
      val goals =
        Local_Defs.fold ctxt transport_defs transport_per_start_thm
        |> Thm.prems_of
        |> map (rpair [])
    in goals end

  fun setup_goals_whitebox ctxt (yT, L, R, cx, y) maxidx =
    let
      val (r, _) = UUtil.fresh_var "r" dummyT maxidx
      (*check*)
      val Galois =
        mk_hom_Galois (Thm.typ_of_cterm cx) yT L R r (Thm.term_of cx) y
        |> Syntax.check_term ctxt
      val goal = Util.mk_judgement Galois |> rpair []
    in [goal] end

  fun setup_proof ((((binding, opt_yT, mixfix), params), unfolds), whitebox) lthy =
    let
      val ctxt = Util.set_proof_mode_schematic lthy
      (*type of transported term*)
      val yT = Option.map (Syntax.read_typ ctxt) opt_yT |> the_default dummyT
      (*other parameters*)
      val {L = optL, R = optR, x = SOME x, y = opty} =
        fold set_cmd_param params empty_cmd_params
      (**term to transport**)
      val unfolds = map (Proof_Context.get_fact ctxt o fst) unfolds |> flat
      val cx =
        (***read term***)
        Syntax.read_term ctxt x |> Thm.cterm_of ctxt
        (***unfold passed theorems***)
        |> Drule.cterm_rule (Local_Defs.unfold ctxt unfolds)
      (**transport relations and transport term goal**)
      val ([L, R, y], maxidx) =
        let
          (***configuration***)
          val opts = [optL, optR, opty]
          val opts_default_names = ["L", "R", "y"]
          val opts_constraints =
            [Util.mk_rel_type (Thm.typ_of_cterm cx), Util.mk_rel_type yT, yT]
            |> map Type.constraint
          (***parse***)
          val opts = map (Syntax.parse_term ctxt |> Option.map) opts
          val params_maxidx = Util.list_max
            (the_default ~1 o Option.map Term.maxidx_of_term)
            (Thm.maxidx_of_cterm cx) opts
          fun create_var (NONE, n) maxidx =
                UUtil.fresh_var n dummyT params_maxidx ||> Integer.max maxidx
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
    -- cmd_params_parser
    (*optionally pass unfold theorems in case of white-box transports*)
    -- Scan.optional (Parse.reserved "unfold" |-- Parse.thms1) []
    (*use a bang "!" to start white-box transport mode (experimental)*)
    -- Parse.opt_bang

  val _ =
    Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>transport_term\<close>
      "transport of definition" (parse_strings >> setup_proof)
\<close>

text \<open>The following sets up an experimental white-box prover; but it
can be ignored as it is not very functional at the moment.\<close>
lemmas Fun_Rel_relD = Dep_Fun_Rel_relD[where ?S="\<lambda>_ _. S" for S]
declare Fun_Rel_relD[transport_related_intro]

ML\<open>
  fun transport_related_tac ctxt =
    let
      val transport_related_intros = Transport_Related_Intros.get ctxt
      val resolve_tac = any_unify_hints_resolve_tac
    in REPEAT1 o resolve_tac transport_related_intros ctxt end
\<close>

method_setup transport_related_prover =
  \<open>Scan.succeed (SIMPLE_METHOD o REPEAT_SOME o transport_related_tac)\<close>
  "Relatedness prover for Transport"


end
