\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Generic Compositions\<close>
theory Transport_Compositions_Generic
  imports
    Transport_Compositions_Generic_Galois_Equivalence
    Transport_Compositions_Generic_Galois_Relator
    Transport_Compositions_Generic_Order_Base
    Transport_Compositions_Generic_Order_Equivalence
begin

subsubsection \<open>Summary of Main Results\<close>

paragraph \<open>Closure of Order and Galois Concepts\<close>

context transport_comp
begin

interpretation flip : transport_comp R2 L2 r2 l2 R1 L1 r1 l1 .

theorem preordered_galois_connection_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "preorder_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  and "in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)" and "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  using assms
  by (auto elim!: g1.galois_equivalenceE g2.galois_equivalenceE
    intro!: galois_connection_left_right_if_galois_equivalenceI
      preorder_on_in_field_leftI flip.preorder_on_in_field_leftI
      mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le
      flip.mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le
      in_codom_eq_in_dom_if_reflexive_on_in_field)

theorem preordered_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "preorder_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R2\<^esub>)) (\<le>\<^bsub>R2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  and "in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  and "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)" and "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  using assms by (auto intro!: galois_equivalence_if_galois_equivalenceI
    preordered_galois_connection_if_galois_equivalenceI(2-3))

theorem preordered_order_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)" "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)" "transitive (\<le>\<^bsub>R2\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>))"
  and "in_codom ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>)) \<le> in_codom (\<le>\<^bsub>L2\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> ((\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>))"
  and "in_codom ((\<le>\<^bsub>L2\<^esub>) \<circ>\<circ> (\<le>\<^bsub>R1\<^esub>) \<circ>\<circ> (\<le>\<^bsub>L2\<^esub>)) \<le> in_codom (\<le>\<^bsub>R1\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  and "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)" and "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  using assms by (auto
    intro!: order_equivalence_if_order_equivalenceI
      preorder_on_in_field_leftI flip.preorder_on_in_field_leftI
      mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le
      flip.mono_in_codom_left_rel_left1_if_in_codom_rel_comp_le
      g1.galois_prop_left_right_if_transitive_if_order_equivalence
      flip.g1.galois_prop_left_right_if_transitive_if_order_equivalence
      g1.half_galois_prop_left_left_right_if_transitive_if_order_equivalence
      flip.g1.half_galois_prop_left_left_right_if_transitive_if_order_equivalence
      in_codom_eq_in_dom_if_reflexive_on_in_field
    intro: preorder_on_in_field_if_transitive_if_rel_equivalence_on
      reflexive_on_in_field_if_transitive_if_rel_equivalence_on
    simp only: g2.order_equivalence_right_left_iff_order_equivalence_left_right)

text \<open>Closure of symmetry can be found in @{thm "symmetric_leftI"},
closure of partial equivalences in @{thm "partial_equivalence_leftI"}.\<close>


paragraph \<open>Simplification of Galois Relation\<close>
thm Galois_eq_Galois_rel_comp_if_galois_connection_if_galois_equivalenceI
text \<open>See
@{thm "Galois_eq_Galois_rel_comp_if_galois_connection_if_galois_equivalenceI"}
and @{thm "Galois_eq_Galois_rel_comp_if_order_equivalenceI"}.\<close>

paragraph \<open>Simplification of Compatibility Assumptions\<close>

text \<open>See @{theory "Transport.Transport_Compositions_Generic_Base"}.\<close>

end


end