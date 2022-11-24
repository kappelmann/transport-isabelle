\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Galois Equivalence\<close>
theory Transport_Functions_Galois_Equivalence
  imports
    Transport_Functions_Galois_Connection
begin

context transport_Refl_Rel_Dep_Fun_Rel_rel
begin

context
begin

interpretation flip : transport_Refl_Rel_Dep_Fun_Rel_rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.g1.counit \<equiv> \<eta>\<^sub>1" and "flip.g1.unit \<equiv> \<epsilon>\<^sub>1"
  by (simp_all only: g1.flip_counit_eq_unit g1.flip_unit_eq_counit)

lemma galois_equivalence_if_galois_equivalenceI:
  assumes galois_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and galois_equiv2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow>
    ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and L2_le1: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and L2_unit_le1: "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) \<le> (\<le>\<^bsub>L2 x x\<^esub>)"
  and L2_le2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and L2_unit_le2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and R2_le1: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x2' x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and R2_counit_le1: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and R2_le2: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and R2_counit_le2: "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) \<le> (\<le>\<^bsub>R2 x' x'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x1' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>) (l2\<^bsub>x2' (r1 x2')\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) x\<^esub>) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>) (r2\<^bsub>(r1 x') x'\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  note g1.galois_equivalenceE[elim!]
  have "((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)"
    if "x \<le>\<^bsub>L1\<^esub> x" for x
  proof (intro galois_prop.half_galois_prop_leftI)
    interpret g : galois "(\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub> )" "(\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)" "r2\<^bsub>x (l1 x)\<^esub>" "l2\<^bsub>(l1 x) x\<^esub>" .
    fix y y' assume "in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) y"
    with L2_unit_le1 have "in_codom (\<le>\<^bsub>L2 x x\<^esub>) y" using \<open>x \<le>\<^bsub>L1\<^esub> x\<close> by blast
    moreover from galois_equiv1 \<open>x \<le>\<^bsub>L1\<^esub> x\<close>  have "x \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x"
      by (intro g1.rel_unit_if_left_rel_if_galois_connection) blast
    ultimately have "in_codom (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) y" using L2_le2 by blast
    moreover assume "y' \<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub> l2\<^bsub>(l1 x) x\<^esub> y"
    ultimately have "r2\<^bsub>x (l1 x)\<^esub> y' \<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub> y"
    proof (intro g.half_galois_prop_leftD)
      from \<open>x \<le>\<^bsub>L1\<^esub> x\<close> galois_equiv1 have "x \<^bsub>L1\<^esub>\<lessapprox> l1 x"
        by (intro g1.Galois_left_if_left_relI) auto
      with galois_equiv2 have "((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)"
        by (auto simp: g2.galois_equivalence_right_left_iff_galois_equivalence_left_right)
      then show "((\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)" by blast
    qed
    with L2_unit_le2 have "r2\<^bsub>x (l1 x)\<^esub> y' \<le>\<^bsub>L2 x x\<^esub> y" using \<open>x \<le>\<^bsub>L1\<^esub> x\<close> by blast
    moreover from galois_equiv1 \<open>x \<le>\<^bsub>L1\<^esub> x\<close> have "\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> x"
      by (intro flip.g1.counit_rel_if_right_rel_if_galois_connection) blast
    ultimately show "r2\<^bsub>x (l1 x)\<^esub> y' \<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub> y" using L2_le1 by blast
  qed
  moreover have "((\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>) (l2\<^bsub>x' (r1 x')\<^esub>)"
    if "x' \<le>\<^bsub>R1\<^esub> x'" for x'
  proof (intro galois_prop.half_galois_prop_rightI)
    interpret g :
      galois "(\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>)" "(\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)" "r2\<^bsub>(r1 x') x'\<^esub>" "l2\<^bsub>x' (r1 x')\<^esub>" .
    fix y y' assume "in_dom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) y'"
    with R2_counit_le2 have "in_dom (\<le>\<^bsub>R2 x' x'\<^esub>) y'" using \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close> by blast
    moreover from galois_equiv1 \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close> have "\<epsilon>\<^sub>1 x' \<le>\<^bsub>R1\<^esub> x'"
      by (intro g1.counit_rel_if_right_rel_if_galois_connection) blast
    ultimately have "in_dom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) y'" using R2_le1 by blast
    moreover assume "r2\<^bsub>(r1 x') x'\<^esub> y' \<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub> y"
    ultimately have "y' \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub> l2\<^bsub>x' (r1 x')\<^esub> y"
    proof (intro g.half_galois_prop_rightD)
      from \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close> galois_equiv1 have "r1 x' \<^bsub>L1\<^esub>\<lessapprox> x'"
        by (intro g1.right_Galois_if_right_relI) blast
      with galois_equiv2 have
        "((\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>) (l2\<^bsub>x' (r1 x')\<^esub>)"
        by (auto simp: g2.galois_equivalence_right_left_iff_galois_equivalence_left_right)
      then show "((\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') x'\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>) (l2\<^bsub>x' (r1 x')\<^esub>)"
        by blast
    qed
    with R2_counit_le1 have "y' \<le>\<^bsub>R2 x' x'\<^esub> l2\<^bsub>x' (r1 x')\<^esub> y" using \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close> by blast
    moreover from galois_equiv1 \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close> have "x' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'"
      by (intro flip.g1.rel_unit_if_left_rel_if_galois_connection) blast
    ultimately show "y' \<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub> l2\<^bsub>x' (r1 x')\<^esub> y" using R2_le2 by blast
  qed
  moreover from galois_equiv2 have "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow>
    ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<stileturn> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)" by blast
  moreover from galois_equiv1 galois_equiv2 have
    "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow>
      ((\<le>\<^bsub>L2 (r1 x1') (r1 x2')\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)) (l2\<^bsub>x2' (r1 x1')\<^esub>)"
    by (intro t.mono_wrt_rel_left_mono_asm_if_mono_wrt_rel) auto
  moreover from galois_equiv1 galois_equiv2 have
    "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
    by (intro t.mono_wrt_rel_right_mono_asm_if_mono_wrt_relI) auto
  ultimately show ?thesis using assms
    by (intro galois_equivalenceI
      galois_connection_left_right_if_galois_connectionI flip.galois_prop_left_rightI'
      t.mono_wrt_rel_left_if_transitiveI t.mono_wrt_rel_right_if_transitiveI)
    (auto intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom
      in_field_if_in_codom)
qed

corollary galois_equivalence_if_galois_equivalenceI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) \<le> (\<le>\<^bsub>L2 x x\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x2' x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> (\<le>\<^bsub>R2 x1' x1'\<^esub>) \<le> (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow> (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) \<le> (\<le>\<^bsub>R2 x' x'\<^esub>)"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_equivalence_if_galois_equivalenceI
    galois_connection_left_right_if_galois_connection_mono_assms_leftI
    galois_connection_left_right_if_galois_connection_mono_assms_rightI
    galois_connection_left_right_if_galois_connection_mono_2_assms_leftI
    galois_connection_left_right_if_galois_connection_mono_2_assms_rightI)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom
    in_field_if_in_codom)

corollary galois_equivalence_if_mono_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | \<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> x1] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | \<epsilon>\<^sub>1 x2' \<le>\<^bsub>R1\<^esub> x1'] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | (x2' \<le>\<^bsub>R1\<^esub> x3' \<and> x4' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x3')] \<Rrightarrow> (\<ge>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x'. x' \<le>\<^bsub>R1\<^esub> x' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>)) (r2\<^bsub>(r1 x') x'\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro galois_equivalence_if_galois_equivalenceI'
    galois_prop_left_right_le_assms_left_if_galois_propI
    flip.galois_prop_left_right_le_assms_left_if_galois_propI
    galois_prop_left_right_le_assms_right_if_galois_propI
    flip.galois_prop_left_right_le_assms_right_if_galois_propI)
  auto

lemma galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI:
  assumes galois_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and preorder_L1: "preorder_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and mono_L2: "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  shows "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | \<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> x1] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2" (is ?goal1)
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3)] \<Rrightarrow> (\<ge>)) L2" (is ?goal2)
proof -
  show ?goal1
  proof (intro dep_mono_wrt_relI rel_if_if_impI Dep_Fun_Rel_relI)
    fix x1 x2 x3 x4 assume "x1 \<le>\<^bsub>L1\<^esub> x2"
    moreover with galois_equiv1 preorder_L1 have "x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2"
      by (blast intro: g1.rel_unit_if_reflexive_on_if_galois_connection)
    moreover assume "\<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> x1"
    ultimately have "x2 \<equiv>\<^bsub>L1\<^esub> x1" using preorder_L1 by blast
    moreover assume "x3 \<le>\<^bsub>L1\<^esub> x4" "x2 \<le>\<^bsub>L1\<^esub> x3"
    ultimately show "(\<le>\<^bsub>L2 x1 x3\<^esub>) \<le> (\<le>\<^bsub>L2 x2 x4\<^esub>)" using preorder_L1 mono_L2 by blast
  qed
  show ?goal2
  proof (intro dep_mono_wrt_relI rel_if_if_impI Dep_Fun_Rel_relI)
    fix x1 x2 x3 x4 presume "x3 \<le>\<^bsub>L1\<^esub> x4" "x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3"
    moreover with galois_equiv1 preorder_L1 have "\<eta>\<^sub>1 x3 \<le>\<^bsub>L1\<^esub> x3"
      by (blast intro: flip.g1.counit_rel_if_reflexive_on_if_galois_connection)
    ultimately have "x3 \<equiv>\<^bsub>L1\<^esub> x4" using preorder_L1 by blast
    moreover presume "x1 \<le>\<^bsub>L1\<^esub> x2" "x2 \<le>\<^bsub>L1\<^esub> x3"
    ultimately show "(\<le>\<^bsub>L2 x2 x4\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x3\<^esub>)" using preorder_L1 mono_L2 by fast
  qed auto
qed

end

interpretation flip : transport_Refl_Rel_Dep_Fun_Rel_rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.g1.counit \<equiv> \<eta>\<^sub>1" and "flip.g1.unit \<equiv> \<epsilon>\<^sub>1"
  by (simp_all only: g1.flip_counit_eq_unit g1.flip_unit_eq_counit)

theorem galois_equivalence_if_mono_if_galois_equivalenceI':
  assumes galois_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and preorder_L1: "preorder_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and preorder_R1: "preorder_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and mono_L2: "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and mono_R2: "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and mono_l2: "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and mono_r2: "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  have "([in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub>)) (l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub>) (l2\<^bsub>(l1 x) x\<^esub>)"
    if "x \<le>\<^bsub>L1\<^esub> x" for x
  proof (intro Dep_Fun_Rel_predI)
    fix y assume "in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) y"
    moreover from \<open>x \<le>\<^bsub>L1\<^esub> x\<close> galois_equiv1 preorder_L1 have "x \<equiv>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x"
      by (blast intro: bi_related_if_rel_equivalence_on
        g1.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence)
    moreover with preorder_L1 have "\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x" by blast
    ultimately have "in_codom (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) (\<eta>\<^sub>1 x)\<^esub>) y" using mono_L2 by blast
    moreover from \<open>x \<le>\<^bsub>L1\<^esub> x\<close> galois_equiv1
      have "l1 x \<le>\<^bsub>R1\<^esub> l1 x" "\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> x" "x \<^bsub>L1\<^esub>\<lessapprox> l1 x"
      by (blast intro: g1.Galois_left_if_left_relI
        flip.g1.counit_rel_if_right_rel_if_galois_connection)+
    moreover note
      Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_l2 \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close>] \<open>\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> x\<close>]
    ultimately have "l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y \<le>\<^bsub>R2 (\<epsilon>\<^sub>1 (l1 x)) (l1 x)\<^esub> l2\<^bsub>(l1 x) x\<^esub> y" by auto
    moreover note \<open>l1 x \<le>\<^bsub>R1\<^esub> l1 x\<close>
    moreover with galois_equiv1 preorder_R1 have "l1 x \<equiv>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 (l1 x)"
      by (blast intro: bi_related_if_rel_equivalence_on
        flip.g1.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence)
    ultimately show "l2\<^bsub>(l1 x) (\<eta>\<^sub>1 x)\<^esub> y \<le>\<^bsub>R2 (l1 x) (l1 x)\<^esub> l2\<^bsub>(l1 x) x\<^esub> y"
      using mono_R2 by blast
  qed
  moreover have "([in_dom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub>))
    (r2\<^bsub>(r1 x') x'\<^esub>) (r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub>)"
    if "x' \<le>\<^bsub>R1\<^esub> x'" for x'
  proof (intro Dep_Fun_Rel_predI)
    fix y assume "in_dom (\<le>\<^bsub>R2 x' (\<epsilon>\<^sub>1 x')\<^esub>) y"
    moreover from \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close> galois_equiv1 preorder_R1 have "x' \<equiv>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'"
      by (blast intro: bi_related_if_rel_equivalence_on
        flip.g1.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence)
    moreover with preorder_R1 have "\<epsilon>\<^sub>1 x' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'" by blast
    ultimately have "in_dom (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x') (\<epsilon>\<^sub>1 x')\<^esub>) y" using mono_R2 by blast
    moreover from \<open>x' \<le>\<^bsub>R1\<^esub> x'\<close> galois_equiv1
      have "r1 x' \<le>\<^bsub>L1\<^esub> r1 x'" "x' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'" "r1 x' \<^bsub>L1\<^esub>\<lessapprox> x'"
      by (blast intro: g1.right_Galois_if_right_relI
        flip.g1.rel_unit_if_left_rel_if_galois_connection)+
    moreover note
      Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_r2 \<open>r1 x' \<le>\<^bsub>L1\<^esub> r1 x'\<close>] \<open>x' \<le>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x'\<close>]
    ultimately have "r2\<^bsub>(r1 x') x'\<^esub> y \<le>\<^bsub>L2 (r1 x') (\<eta>\<^sub>1 (r1 x'))\<^esub> r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y" by auto
    moreover note \<open>r1 x' \<le>\<^bsub>L1\<^esub> r1 x'\<close>
    moreover with galois_equiv1 preorder_R1 have "r1 x' \<equiv>\<^bsub>L1\<^esub> \<eta>\<^sub>1 (r1 x')"
      by (blast intro: bi_related_if_rel_equivalence_on
        g1.rel_equivalence_on_unit_if_reflexive_on_if_galois_equivalence)
    ultimately show "r2\<^bsub>(r1 x') x'\<^esub> y \<le>\<^bsub>L2 (r1 x') (r1 x')\<^esub> r2\<^bsub>(r1 x') (\<epsilon>\<^sub>1 x')\<^esub> y"
      using mono_L2 by blast
  qed
  ultimately show ?thesis
    using assms by (intro galois_equivalence_if_mono_if_galois_equivalenceI
      galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI
      flip.galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI)
    (auto simp: g1.galois_equivalence_right_left_iff_galois_equivalence_left_right)
qed

corollary galois_equivalence_if_order_equivalenceI:
  assumes order_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and trans_L1: "transitive (\<le>\<^bsub>L1\<^esub>)"
  and trans_R1: "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and trans_R2: "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  from order_equiv1 have "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
    using trans_L1 trans_R1
    by (intro g1.galois_equivalence_left_right_if_transitive_if_order_equivalence)
    auto
  moreover then have "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> transitive (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)"
    by (intro trans_R2) blast
  ultimately show ?thesis using assms
    by (intro galois_equivalence_if_mono_if_galois_equivalenceI'
      g2.galois_equivalence_left_right_if_transitive_if_order_equivalence
      g1.preorder_on_in_field_left_if_transitive_if_order_equivalence
      flip.g1.preorder_on_in_field_left_if_transitive_if_order_equivalence)
    auto
qed

end


end