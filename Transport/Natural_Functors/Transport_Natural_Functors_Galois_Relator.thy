\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Galois Relator\<close>
theory Transport_Natural_Functors_Galois_Relator
  imports
    Transport_Natural_Functors_Base
begin

context transport_natural_functor
begin

lemma Galois_Frel_Galois: "(\<^bsub>L\<^esub>\<lessapprox>) \<le> Frel (\<^bsub>L1\<^esub>\<lessapprox>) (\<^bsub>L2\<^esub>\<lessapprox>) (\<^bsub>L3\<^esub>\<lessapprox>)"
  apply (rule le_relI)
  apply (erule GaloisE)
  apply (unfold left_rel_eq_Frel right_rel_eq_Frel right_eq_Fmap)
  apply (subst (asm) in_codom_Frel_eq_Fpred_in_codom)
  apply (erule FpredE)
  apply (subst (asm) Frel_Fmap_eq2)
  apply (rule Frel_mono_strong,
    assumption;
    rule g1.GaloisI g2.GaloisI g3.GaloisI;
    assumption)
  done

lemma Frel_Galois_le_Galois:
  "Frel (\<^bsub>L1\<^esub>\<lessapprox>) (\<^bsub>L2\<^esub>\<lessapprox>) (\<^bsub>L3\<^esub>\<lessapprox>) \<le> (\<^bsub>L\<^esub>\<lessapprox>)"
  apply (rule le_relI)
  apply (unfold g1.Galois_iff_in_codom_and_left_rel_right
    g2.Galois_iff_in_codom_and_left_rel_right
    g3.Galois_iff_in_codom_and_left_rel_right)
  apply (fold
    restrict_right_eq[of "\<lambda>x y. x \<le>\<^bsub>L1\<^esub> r1 y" "in_codom (\<le>\<^bsub>R1\<^esub>)",
      unfolded restrict_left_pred_def rel_inv_iff_rel]
    restrict_right_eq[of "\<lambda>x y. x \<le>\<^bsub>L2\<^esub> r2 y" "in_codom (\<le>\<^bsub>R2\<^esub>)",
      unfolded restrict_left_pred_def rel_inv_iff_rel]
    restrict_right_eq[of "\<lambda>x y. x \<le>\<^bsub>L3\<^esub> r3 y" "in_codom (\<le>\<^bsub>R3\<^esub>)",
      unfolded restrict_left_pred_def rel_inv_iff_rel])
  apply (subst (asm) Frel_restrict_right_Fpred_eq_Frel_restrict_right[symmetric])
  apply (erule restrict_rightE)
  apply (subst (asm) in_codom_Frel_eq_Fpred_in_codom[symmetric])
  apply (erule in_codomE)
  apply (rule GaloisI)
    apply (rule in_codomI)
    apply (subst right_rel_eq_Frel)
    apply assumption
    apply (unfold left_rel_eq_Frel right_eq_Fmap Frel_Fmap_eq2)
    apply assumption
  done

corollary Galois_eq_Frel_Galois: "(\<^bsub>L\<^esub>\<lessapprox>) = Frel (\<^bsub>L1\<^esub>\<lessapprox>) (\<^bsub>L2\<^esub>\<lessapprox>) (\<^bsub>L3\<^esub>\<lessapprox>)"
  by (intro antisym Galois_Frel_Galois Frel_Galois_le_Galois)

end


end