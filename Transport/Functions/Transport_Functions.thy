\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transport For Functions\<close>
theory Transport_Functions
  imports
    Transport_Functions_Galois_Equivalence
    Transport_Functions_Galois_Relator
    Transport_Functions_Order_Base
    Transport_Functions_Order_Equivalence
begin

subsubsection \<open>Summary of Main Results\<close>

paragraph \<open>Dependent Function Relator\<close>

context transport_Refl_Rel_Dep_Fun_Rel_rel
begin

interpretation flip : transport_Refl_Rel_Dep_Fun_Rel_rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.g1.counit \<equiv> \<eta>\<^sub>1" and "flip.g1.unit \<equiv> \<epsilon>\<^sub>1"
  by (simp_all only: g1.flip_counit_eq_unit g1.flip_unit_eq_counit)

subparagraph \<open>Closure of Order and Galois Concepts\<close>

theorem preordered_galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<stileturn> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([_ x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | \<epsilon>\<^sub>1 x2' \<le>\<^bsub>R1\<^esub> x1'] \<Rrightarrow>\<^sub>m [x3' _ \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)" and "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  using assms by (auto
    intro!: galois_connection_left_right_if_mono_if_galois_connectionI'
      preorder_on_in_field_leftI flip.preorder_on_in_field_leftI
      t.transitive_leftI' flip.t.transitive_leftI
      galois_prop_left_right_le_assms_left_if_galois_propI
      galois_prop_left_right_le_assms_right_if_galois_propI
    intro: reflexive_on_if_le_pred_if_reflexive_on
      in_field_if_in_dom in_field_if_in_codom)

theorem preordered_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "preorder_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  and "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)" and "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  using assms by (auto
    intro!: galois_equivalence_if_mono_if_galois_equivalenceI'
      preordered_galois_connectionI(2-3)
      galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI
      flip.galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI)

theorem preordered_order_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)" and "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>R1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1 x2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  and "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)" and "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  using assms by (auto
    intro!: order_equivalence_if_mono_if_order_equivalenceI'
      preorder_on_in_field_leftI flip.preorder_on_in_field_leftI
      t.transitive_leftI' flip.t.transitive_leftI
      galois_prop_left_right_le_assms_left_if_galois_propI
      galois_prop_left_right_le_assms_right_if_galois_propI
      galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI
      flip.galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI
      g1.galois_connection_left_right_if_transitive_if_order_equivalence
      g1.galois_equivalence_left_right_if_transitive_if_order_equivalence
      flip.g1.galois_equivalence_left_right_if_transitive_if_order_equivalence
      g1.preorder_on_in_field_left_if_transitive_if_order_equivalence
      flip.g1.preorder_on_in_field_left_if_transitive_if_order_equivalence
      reflexive_on_in_field_if_transitive_if_rel_equivalence_on
    intro: reflexive_on_if_le_pred_if_reflexive_on
      in_field_if_in_dom in_field_if_in_codom)

text \<open>Closure of symmetry can be found in @{thm "symmetric_leftI"},
closure of partial equivalences in @{thm "partial_equivalence_leftI"}.\<close>


subparagraph \<open>Simplification of Galois Relation\<close>

text \<open>See
@{thm "Galois_eq_Dep_Fun_Rel_rel_Galois_restrict_if_mono_if_galois_connectionI"},
@{thm "Galois_eq_Dep_Fun_Rel_rel_Galois_restrict_if_galois_equivalenceI"},
and @{thm "Galois_eq_Dep_Fun_Rel_rel_Galois_restrict_if_order_equivalenceI"}.\<close>

end


paragraph \<open>Non-Dependent Function Relator\<close>

context transport_Refl_Rel_Fun_Rel_rel
begin

context
begin

interpretation flip : transport_Refl_Rel_Fun_Rel_rel R1 L1 r1 l1 R2 L2 r2 l2 .

subparagraph \<open>Closure of Order and Galois Concepts\<close>

theorem preordered_galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)" "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<stileturn> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)" "transitive (\<le>\<^bsub>R2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)" and "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  using assms by (auto intro!:
    rdfr.galois_connectionI rdfr.galois_prop_left_rightI
    rdfr.mono_wrt_rel_leftI flip.rdfr.mono_wrt_rel_leftI
    rdfr.t.mono_wrt_rel_leftI rdfr.t.mono_wrt_rel_rightI
    rdfr.preorder_on_in_field_leftI
    flip.rdfr.preorder_on_in_field_leftI
    rdfr.t.transitive_leftI'
    flip.rdfr.t.transitive_leftI)

end

interpretation flip : transport_Refl_Rel_Fun_Rel_rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.rdfr.unit \<equiv> \<epsilon>" and "flip.rdfr.g1.unit \<equiv> \<epsilon>\<^sub>1"
  and "flip.rdfr.counit \<equiv> \<eta>" and "flip.rdfr.g1.counit \<equiv> \<eta>\<^sub>1"
  and "flip.rdfr.g2.unit \<equiv> \<epsilon>\<^sub>2"
  by (simp_all add: order_functors.flip_counit_eq_unit)

theorem preordered_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)" "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)" "transitive (\<le>\<^bsub>R2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  and "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)" and "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  using assms by (auto elim!: rdfr.g2.galois_equivalenceE
    intro!: rdfr.galois_equivalenceI
      preordered_galois_connectionI
      flip.rdfr.galois_prop_left_rightI
      rdfr.t.mono_wrt_rel_leftI rdfr.t.mono_wrt_rel_rightI
    intro: reflexive_on_if_le_pred_if_reflexive_on
      in_field_if_in_dom in_field_if_in_codom)

theorem preordered_order_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)" "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)" "transitive (\<le>\<^bsub>R2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  and "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)" and "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  using assms by (auto
    intro!: order_functors.order_equivalenceI
      rdfr.rel_equivalence_on_unitI
      flip.rdfr.rel_equivalence_on_unitI
      rdfr.mono_wrt_rel_leftI flip.rdfr.mono_wrt_rel_leftI
      rdfr.t.mono_wrt_rel_leftI rdfr.t.mono_wrt_rel_rightI
      rdfr.preorder_on_in_field_leftI
      flip.rdfr.preorder_on_in_field_leftI
      rdfr.t.transitive_leftI'
      flip.rdfr.t.transitive_leftI
      reflexive_on_in_field_if_transitive_if_rel_equivalence_on
    intro: reflexive_on_if_le_pred_if_reflexive_on
      in_field_if_in_dom in_field_if_in_codom)

text \<open>Closure of symmetry can be found in @{thm "symmetric_leftI"},
closure of partial equivalences in @{thm "partial_equivalence_leftI"}.\<close>


subparagraph \<open>Simplification of Galois Relation\<close>

text \<open>See @{thm "Galois_eq_Fun_Rel_rel_Galois_restrictI"}.\<close>

end

end