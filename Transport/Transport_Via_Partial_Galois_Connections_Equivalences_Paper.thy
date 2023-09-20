section \<open>Transport Paper Guide\<close>
theory Transport_Via_Partial_Galois_Connections_Equivalences_Paper
  imports
    Transport
    Transport_Natural_Functors
    Transport_Partial_Quotient_Types
    Transport_Prototype
    Transport_Lists_Sets_Examples
    Transport_Dep_Fun_Rel_Examples
    Transport_Typedef_Base
begin

text \<open>

\<bullet> Section 3.1: Order basics can be found in
  @{theory "Transport.Binary_Relation_Properties"},
  @{theory "Transport.Preorders"},
  @{theory "Transport.Partial_Equivalence_Relations"},
  @{theory "Transport.Equivalence_Relations"}, and
  @{theory "Transport.Order_Functions_Base"}.
Theorem
\<bullet> Section 3.2: Function relators and monotonicity can be found in
  @{theory "Transport.Function_Relators"} and
  @{theory "Transport.Functions_Monotone"}

\<bullet> Section 3.3: Galois relator can be found in
  @{theory "Transport.Galois_Relator_Base"}.
  \<bullet> Lemma 1: @{theory "Transport.Transport_Partial_Quotient_Types"}
  (*results from Appendix*)
  \<bullet> Lemma 3: @{thm "galois_prop.Galois_right_iff_left_Galois_if_galois_prop"}

\<bullet> Section 3.4: Partial Galois Connections and Equivalences can be found in
  @{theory "Transport.Half_Galois_Property"},
  @{theory "Transport.Galois_Property"},
  @{theory "Transport.Galois_Connections"},
  @{theory "Transport.Galois_Equivalences"}, and
  @{theory "Transport.Order_Equivalences"}.
  \<bullet> Lemma 2: @{theory "Transport.Transport_Partial_Quotient_Types"}
  (*results from Appendix*)
  \<bullet> Lemma 4: @{thm "galois.galois_equivalence_left_right_if_transitive_if_order_equivalence"}
  \<bullet> Lemma 5: @{thm "galois.order_equivalence_if_reflexive_on_in_field_if_galois_equivalence"}

\<bullet> Section 4.1: Closure (Dependent) Function Relator can be found in
  @{dir "Functions"}.
  \<bullet> Monotone function relator @{theory "Transport.Monotone_Function_Relator"}.
  \<bullet> Setup of construction @{theory "Transport.Transport_Functions_Base"}.
  \<bullet> Theorem 1: see @{theory "Transport.Transport_Functions"}
  \<bullet> Theorem 2: see @{thm "transport_Mono_Dep_Fun_Rel.left_Galois_iff_Dep_Fun_Rel_left_Galois_if_preorder_equivalenceI'"}
  (*results from Appendix*)
  \<bullet> Lemma 6: @{thm "transport_Mono_Fun_Rel.galois_connection_left_rightI"}
  \<bullet> Lemma 7: @{thm "transport_Mono_Fun_Rel.left_Galois_iff_Fun_Rel_left_GaloisI"}
  \<bullet> Theorem 7: @{thm "transport_Mono_Dep_Fun_Rel.galois_connection_left_right_if_mono_if_galois_connectionI'"}
  \<bullet> Theorem 8: @{thm "transport_Mono_Dep_Fun_Rel.left_Galois_iff_Dep_Fun_Rel_left_Galois_if_mono_if_galois_connectionI'"}
  \<bullet> Lemma 8 @{thm "transport_Mono_Dep_Fun_Rel.left_rel_eq_tdfr_leftI_if_equivalencesI"}
  \<bullet> Lemma 9: @{thm "transport_Mono_Fun_Rel.left_rel_eq_tfr_leftI"}

\<bullet> Section 4.2: Closure Natural Functors can be found in
  @{dir "Natural_Functors"}.
  \<bullet> Theorem 3: see @{theory "Transport.Transport_Natural_Functors"}
  \<bullet> Theorem 4: @{thm "transport_natural_functor.left_Galois_eq_Frel_left_Galois"}


\<bullet> Section 4.3: Closure Compositions can be found in @{dir "Compositions"}.
  \<bullet> Setup for simple case in @{theory "Transport.Transport_Compositions_Agree_Base"}
  \<bullet> Setup for generic case in @{theory "Transport.Transport_Compositions_Generic_Base"}
  \<bullet> Theorem 5: @{thm "transport_comp.preorder_equivalenceI"} and
    @{thm "transport_comp.partial_equivalence_rel_equivalenceI"}
  \<bullet> Theorem 6: @{thm "transport_comp.left_Galois_eq_comp_left_GaloisI"}
  (*results from Appendix*)
  \<bullet> Theorem 9: see @{dir "Compositions/Agree"}, results in
    @{locale transport_comp_same}.
  \<bullet> Theorem 10: @{thm "transport_comp.galois_connection_left_right_if_galois_equivalenceI"}
  \<bullet> Theorem 11: @{thm "transport_comp.left_Galois_eq_comp_left_GaloisI'"}

\<bullet> Section 5:
  \<bullet> Implementation @{theory "Transport.Transport_Prototype"}:
    Note: the command "trp" from the paper is called @{command trp_term} and the
    method "trprover" is called "trp_term_prover".
  \<bullet> Example 1: @{theory "Transport.Transport_Lists_Sets_Examples"}
  \<bullet> Example 2: @{theory "Transport.Transport_Dep_Fun_Rel_Examples"}
  TODO
  \<bullet> Example 3: theory "Transport.Transport_Set_Extension"

\<bullet> Proof: Partial Quotient Types are a special case:
  @{theory "Transport.Transport_Partial_Quotient_Types"}
\<bullet> Proof: Typedefs are a special case:
  @{theory "Transport.Transport_Typedef_Base"}
\<bullet> Proof: Set-Extensions are a special case:
  TODO
  theory "Transport.Set_Extensions_Transport"
\<bullet> Proof: Bijections as special case:
  @{theory "Transport.Transport_Bijections"}
\<close>

end
