\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transport via Equivalences on PERs\<close>
theory Transport_PER
  imports
    Transport.Transport
    Transport_Rel_If
    ML_Unification.ML_Unification
    ML_Unification.ML_Unification_Resolution
    Logging.ML_Attributes
  keywords "transport_term" :: thy_goal_defn
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

The package provides a command @{command "transport_term"}, which sets up the
required goals to prove a given term. See the examples in this directory for
some use cases and refer to the paper
"Transport via Partial Galois Connections and Equivalences" by Kevin Kappelmann
for more details.\<close>

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

ML_file\<open>transport_util.ML\<close>
ML_file\<open>transport_parse_util.ML\<close>

ML\<open>
  structure Norm = Normalisation
  structure Util = Transport_Util
  structure CUtil = Conversion_Util
  structure UUtil = Unification_Util
  structure PUtil = Transport_Parse_Util
\<close>

ML\<open>
  (* val simp_rhs *)
  val simp_rhs = Simplifier.rewrite #> CUtil.rhs_conv #> CUtil.thm_conv

  (*simplifies the generated definition of a transported term*)
  fun simp_transported_def ctxt simps y_def =
    let
      val ctxt = ctxt addsimps simps
      val y_def_eta_expanded = Util.equality_eta_expand ctxt "x" y_def
    in apply2 (simp_rhs ctxt) (y_def, y_def_eta_expanded) end
\<close>

text \<open>Definitions used by Transport that need to be folded before a PER proof
and unfolded after success.\<close>
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
  val norm_thm_beta_eta = Norm.beta_eta_norm_thm Norm.norm_type_unif Norm.norm_term_unif
  fun unify_hints binders ctxt =
    let
      val unify_types = UUtil.unify_types
      val hints = Unification_Hints.get_hints ctxt
      val unif_hints = Higher_Order_Pattern_Unification.unify
      val norm_term_unif = Norm.norm_term_unif
      val norm_thm_unif = norm_thm_beta_eta
      fun ho_unify ctxt = Higher_Order_Pattern_Unification.e_unify
        unify_types (Unification_Hints.try_hints unif_hints norm_term_unif norm_thm_unif ho_unify hints)
        ctxt
      val unify = First_Order_Unification.e_unify unify_types ho_unify
    in unify binders ctxt end

  (*resoluton with above unifier*)
  val any_unify_hints_resolve_tac = Unify_Resolve.any_unify_resolve_tac
    norm_thm_beta_eta unify_hints

  fun get_theorems_tac f get_theorems ctxt = f (get_theorems ctxt) ctxt
  val get_theorems_resolve_tac = get_theorems_tac any_unify_hints_resolve_tac
\<close>

method_setup resolve_hints =
  \<open>Attrib.thms >> (SIMPLE_METHOD' oo any_unify_hints_resolve_tac)\<close>
  "Resolution with unification hints"

text \<open>Introduction rules for the PER equivalence prover.\<close>
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
    [ML_rattr \<open>Conversion_Util.move_prems_to_front_conv [1] |> CUtil.thm_conv |> K\<close>,
    ML_rattr \<open>Conversion_Util.move_prems_to_front_conv [2,3] |> CUtil.thm_conv |> K\<close>,
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
  "parametricity prover for Transport"

text \<open>Blackbox prover: first derive the PER equivalence, then look for registered domain lemmas.\<close>
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
  transport_id.left_Galois_eq_left[transport_relator_rewrite]
  transport_Fun_Rel.left_Galois_eq_Fun_Rel_left_Galois[transport_relator_rewrite]

ML\<open>
  fun fold_tac thms =
    Tactic_Util.FOCUS_PARAMS_CTXT
      (fn ctxt => PRIMITIVE (Raw_Simplifier.fold_rule (clear_simpset ctxt) thms))

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
  val binding_in_dom = \<^binding>\<open>in_dom\<close>
  val binding_related = \<^binding>\<open>related\<close>
  val binding_related_rewritten = \<^binding>\<open>related'\<close>
  val binding_def_simplified = \<^binding>\<open>eq\<close>
  val binding_def_eta_expanded_simplified = \<^binding>\<open>app_eq\<close>

  fun note_facts (binding, mixfix) ctxt related_thm y binding_thms_attribs =
    let
      val ((_, (_, y_def)), ctxt) =
        Util.create_local_theory_def (binding, mixfix) [] y ctxt
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
            [Util.attrib_to_src Transport_in_dom.add])
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
            [Util.mk_hom_rel_type (Thm.typ_of_cterm cx), Util.mk_hom_rel_type yT, yT]
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

text \<open>The following sets up an experimental white-box prover.\<close>
lemmas related_Fun_Rel_combI = Dep_Fun_Rel_relD[where ?S="\<lambda>_ _. S" for S, rotated]
lemma related_Fun_Rel_lambdaI:
  assumes "\<And>x y. R x y \<Longrightarrow> S (f x) (g y)"
  and "T = (R \<Rrightarrow> S)"
  shows "T f g"
  using assms by blast

ML\<open>
  fun pattern_prefix p =
    let fun bounds_prefix bounds [] = (rev bounds, [])
          | bounds_prefix bounds (t :: ts) =
              if is_Bound t andalso not (member (op =) bounds t)
              then bounds_prefix (t :: bounds) ts
              else (rev bounds, t :: ts)
    in case strip_comb p of
        (v as Var _, args) => let val (bounds, rem_args) = bounds_prefix [] args
          in SOME (list_comb (v, bounds), rem_args) end
      | _ => NONE
    end
  fun higher_order_pattern_match_first_order binders =
    let
      fun fallback binders ctxt (p, t) = case pattern_prefix p of
        SOME (ph, ps) =>
          let val (th, ts) = strip_comb t
            ||> (fn ts => chop (length ts - length ps) ts)
            |> (fn (th, (ts, ts')) => (list_comb (th, ts), ts'))
          in
            if length ts < length ps then K Seq.empty
            else
              UUtil.strip_comb_strip_comb (K o K I) higher_order_pattern_match_first_order
              binders ctxt (ph, th) (ps, ts)
          end
      | NONE => K Seq.empty
    in Higher_Order_Pattern_Unification.e_match UUtil.match_types fallback binders end
  val any_match_hints_resolve_tac = Unify_Resolve.any_unify_resolve_tac
    (Norm.beta_eta_norm_thm Norm.norm_type_match Norm.norm_term_match)
    higher_order_pattern_match_first_order
\<close>

ML\<open>
  val related_comb_tac = any_match_hints_resolve_tac @{thms related_Fun_Rel_combI}
  val related_lambda_tac = any_match_hints_resolve_tac @{thms related_Fun_Rel_lambdaI}
  val related_tac = any_unify_hints_resolve_tac
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
      val (vars, _) = fold_map (uncurry UUtil.fresh_var o apfst Long_Name.base_name) consts maxidx
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
      THEN' TRY o any_unify_hints_resolve_tac @{thms refl} ctxt
    )
\<close>

method_setup transport_whitebox_prover =
  \<open>Scan.succeed (SIMPLE_METHOD' o transport_whitebox_tac)\<close>
  "Whitebox prover for Transport"


end
