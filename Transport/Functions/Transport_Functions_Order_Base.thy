\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Basic Order Properties\<close>
theory Transport_Functions_Order_Base
  imports
    Transport_Functions_Base
begin

paragraph \<open>Dependent Function Relator\<close>

context hom_Dep_Fun_Rel_orders
begin

lemma transitiveI:
  assumes refl: "reflexive_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and R_le_R_if_L: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x1 x1\<^esub>) \<le> (\<le>\<^bsub>R x1 x2\<^esub>)"
  and trans: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "transitive DFR"
proof (intro transitiveI Dep_Fun_Rel_relI)
  fix f1 f2 f3 x1 x2 assume "x1 \<le>\<^bsub>L\<^esub> x2"
  with refl have "x1 \<le>\<^bsub>L\<^esub> x1" by blast
  moreover assume "DFR f1 f2"
  ultimately have "f1 x1 \<le>\<^bsub>R x1 x1\<^esub> f2 x1" by blast
  with R_le_R_if_L have "f1 x1 \<le>\<^bsub>R x1 x2\<^esub> f2 x1" using \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> by blast
  assume "DFR f2 f3"
  with \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> have "f2 x1 \<le>\<^bsub>R x1 x2\<^esub> f3 x2" by blast
  with \<open>f1 x1 \<le>\<^bsub>R x1 x2\<^esub> f2 x1\<close> show "f1 x1 \<le>\<^bsub>R x1 x2\<^esub>  f3 x2"
    using trans \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> by blast
qed

lemma transitiveI':
  assumes refl: "reflexive_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and R_le_R_if_L: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x2 x2\<^esub>) \<le> (\<le>\<^bsub>R x1 x2\<^esub>)"
  and trans: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "transitive DFR"
proof (intro Binary_Relations_Transitive.transitiveI Dep_Fun_Rel_relI)
  fix f1 f2 f3 x1 x2 assume "DFR f1 f2" "x1 \<le>\<^bsub>L\<^esub> x2"
  then have "f1 x1 \<le>\<^bsub>R x1 x2\<^esub> f2 x2" by blast
  from \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> refl have "x2 \<le>\<^bsub>L\<^esub> x2" by blast
  moreover assume "DFR f2 f3"
  ultimately have "f2 x2 \<le>\<^bsub>R x2 x2\<^esub> f3 x2" by blast
  with R_le_R_if_L have "f2 x2 \<le>\<^bsub>R x1 x2\<^esub> f3 x2" using \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> by blast
  with \<open>f1 x1 \<le>\<^bsub>R x1 x2\<^esub> f2 x2\<close> show "f1 x1 \<le>\<^bsub>R x1 x2\<^esub> f3 x2"
    using trans \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> by blast
qed

lemma symmetricI:
  assumes sym_L: "symmetric (\<le>\<^bsub>L\<^esub>)"
  and mono_R: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x1 x2\<^esub>) \<le> (\<le>\<^bsub>R x2 x1\<^esub>)"
  and sym_R: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> symmetric (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "symmetric DFR"
proof (intro symmetricI Dep_Fun_Rel_relI)
  fix f g x y assume "x \<le>\<^bsub>L\<^esub> y"
  with sym_L have "y \<le>\<^bsub>L\<^esub> x" by (rule symmetricD)
  moreover assume "DFR f g"
  ultimately have "f y \<le>\<^bsub>R y x\<^esub> g x" by blast
  with sym_R \<open>y \<le>\<^bsub>L\<^esub> x\<close> have "g x \<le>\<^bsub>R y x\<^esub> f y" by (blast dest: symmetricD)
  with mono_R \<open>y \<le>\<^bsub>L\<^esub> x\<close> show "g x \<le>\<^bsub>R x y\<^esub> f y" by blast
qed

corollary partial_equivalenceI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and sym_L: "symmetric (\<le>\<^bsub>L\<^esub>)"
  and mono_R: "([x1 x2 \<Colon> (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L\<^esub>) | x1 \<le>\<^bsub>L\<^esub> x3] \<Rrightarrow> (\<le>)) R"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> partial_equivalence (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "partial_equivalence DFR"
proof -
  have "(\<le>\<^bsub>R x1 x2\<^esub>) \<le> (\<le>\<^bsub>R x2 x1\<^esub>)" if "x1 \<le>\<^bsub>L\<^esub> x2" for x1 x2
  proof -
    from sym_L \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> have "x2 \<le>\<^bsub>L\<^esub> x1" by (rule symmetricD)
    with mono_R \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> show ?thesis by blast
  qed
  with assms show ?thesis
    by (intro partial_equivalenceI transitiveI symmetricI)
    (auto elim: partial_equivalenceE[OF assms(4)])
qed

end

context transport_Dep_Fun_Rel_rel
begin

lemmas transitive_leftI = dfro1.transitiveI[folded left_rel_eq_Dep_Fun_Rel_rel]
lemmas transitive_leftI' = dfro1.transitiveI'[folded left_rel_eq_Dep_Fun_Rel_rel]
lemmas symmetric_leftI = dfro1.symmetricI[folded left_rel_eq_Dep_Fun_Rel_rel]
lemmas partial_equivalence_leftI = dfro1.partial_equivalenceI
  [folded left_rel_eq_Dep_Fun_Rel_rel]

end


paragraph \<open>Reflexive Relator\<close>

context transport_Refl_Rel_Dep_Fun_Rel_rel
begin

lemmas transitive_leftI = Refl_Rel_transitiveI
  [of t.L, folded left_rel_eq_Refl_Rel]
lemmas reflexive_on_in_field_leftI = Refl_Rel_reflexive_on_in_field[of t.L,
  folded left_rel_eq_Refl_Rel]
lemmas preorder_on_in_field_leftI = Refl_Rel_preorder_on_in_fieldI[of t.L,
  folded left_rel_eq_Refl_Rel]
lemmas symmetric_leftI = Refl_Rel_symmetricI[of t.L,
  OF t.symmetric_leftI, folded left_rel_eq_Refl_Rel]
lemmas partial_equivalence_leftI = Refl_Rel_partial_equivalenceI[of t.L,
  OF t.partial_equivalence_leftI, folded left_rel_eq_Refl_Rel]

end


paragraph \<open>Non-Dependent Function Relator\<close>

context transport_Refl_Rel_Fun_Rel_rel
begin

lemma symmetric_leftI:
  assumes "symmetric (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> symmetric (\<le>\<^bsub>L2\<^esub>)"
  shows "symmetric (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro rdfr.symmetric_leftI) auto

lemma partial_equivalence_leftI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)" "symmetric (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> partial_equivalence (\<le>\<^bsub>L2\<^esub>)"
  shows "partial_equivalence (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro rdfr.partial_equivalence_leftI) auto

end


end