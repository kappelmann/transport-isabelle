(*  Title:      Transport/util.ML
    Author:     Kevin Kappelmann

Utilities used by Transport.
*)

signature TRANSPORT_UTIL =
sig

  (* lists *)
  val list_aggregate : ('a * 'b -> 'b) -> ('c -> 'a) -> 'b -> 'c list -> 'b
  val list_max : ('a -> int) -> int -> 'a list -> int

  (* object logic *)
  val mk_judgement : term -> term
  val dest_judgement : term -> term
  val real_thm_concl : thm -> term
  val cdest_judgement : cterm -> cterm
  val real_thm_cconcl : thm -> cterm
  val boolT : typ

  val mk_rel_type : typ -> typ
  (* conversions *)
  val judgement_conv : conv -> conv

  (* bindings *)
  val concat_bindings : binding list -> binding
  val add_suffix : binding -> binding -> binding

  (* contexts *)
  val set_proof_mode_schematic : Proof.context -> Proof.context

  (* definitions *)
  val create_local_theory_def : binding * mixfix -> Token.src list -> term ->
    local_theory -> (term * (string * thm)) * local_theory
  val equality_eta_expand : Proof.context -> string -> thm -> thm

  (* methods *)
  val split_conjunctions : Method.text

  (* attributes *)
  val attrib_to_src : attribute -> Token.src

end

structure Transport_Util : TRANSPORT_UTIL =
struct

fun list_aggregate aggregate transform = List.foldl (aggregate o apfst transform)
fun list_max f = list_aggregate Int.max f

val mk_judgement = HOLogic.mk_Trueprop
val dest_judgement = HOLogic.dest_Trueprop
val real_thm_concl = dest_judgement o Thm.concl_of
val cdest_judgement = Thm.dest_comb #> snd
val real_thm_cconcl = cdest_judgement o Thm.cconcl_of
val boolT = HOLogic.boolT

fun mk_rel_type T = [T, T] ---> boolT

val judgement_conv = HOLogic.Trueprop_conv

val split_conjunctions =
  Method.Basic (fn _ => SIMPLE_METHOD (HEADGOAL Goal.conjunction_tac))

fun equality_eta_expand ctxt name eq =
  let
    val argTs = Thm.lhs_of eq |> Thm.typ_of_cterm |> binder_types
    val fresh_args = Unification_Util.fresh_vars name argTs (Thm.maxidx_of eq)
      |> map (Thm.cterm_of ctxt) o fst
  in
    fold (fn arg => fn funThm => Drule.fun_cong_rule funThm arg) fresh_args eq
  end

val concat_bindings = Binding.conglomerate
fun add_suffix binding suffix = concat_bindings [binding, suffix]

val set_proof_mode_schematic = Proof_Context.set_mode Proof_Context.mode_schematic

fun create_local_theory_def (binding, mixfix) attribs t =
  Local_Theory.define ((binding, mixfix), ((Thm.def_binding binding, attribs), t))

val attrib_to_src = Attrib.internal o K

end