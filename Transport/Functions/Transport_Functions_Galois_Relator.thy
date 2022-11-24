\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Galois Relator\<close>
theory Transport_Functions_Galois_Relator
  imports
    Transport_Functions_Monotone
begin

paragraph \<open>Dependent Function Relator\<close>

context transport_Dep_Fun_Rel_rel
begin

interpretation flip : transport_Dep_Fun_Rel_rel R1 L1 r1 l1 R2 L2 r2 l2 .

lemma Dep_Fun_Rel_rel_Galois_if_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and mono_r2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and L2_le2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and ge_L2_r2_le2: "\<And>x x' y'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x (l1 x)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x x'\<^esub> y')"
  and trans_L2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "g \<le>\<^bsub>R\<^esub> g"
  and "f \<^bsub>L\<^esub>\<lessapprox> g"
  shows "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
proof (intro Dep_Fun_Rel_relI)
  fix x x' assume "x \<^bsub>L1\<^esub>\<lessapprox> x'"
  show "f x \<^bsub>L2 x x'\<^esub>\<lessapprox> g x'"
  proof (intro g2.GaloisI)
    from \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close> \<open>((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1\<close> have "x \<le>\<^bsub>L1\<^esub> r1 x'" "l1 x \<le>\<^bsub>R1\<^esub> x'"
      by auto
    with \<open>g \<le>\<^bsub>R\<^esub> g\<close> have "g (l1 x) \<le>\<^bsub>R2 (l1 x) x'\<^esub> g x'" by blast
    then show "in_codom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>) (g x')" by blast

    from \<open>f \<^bsub>L\<^esub>\<lessapprox> g\<close> have "f \<le>\<^bsub>L\<^esub> r g" by blast
    moreover from refl_L1 \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close> have "x \<le>\<^bsub>L1\<^esub> x" by blast
    ultimately have "f x \<le>\<^bsub>L2 x x\<^esub> (r g) x" by blast
    with L2_le2 \<open>x \<le>\<^bsub>L1\<^esub> r1 x'\<close> have "f x \<le>\<^bsub>L2 x (r1 x')\<^esub> (r g) x" by blast
    then have "f x \<le>\<^bsub>L2 x (r1 x')\<^esub> r2\<^bsub>x (l1 x)\<^esub> (g (l1 x))" by simp
    with ge_L2_r2_le2 have "f x \<le>\<^bsub>L2 x (r1 x')\<^esub> r2\<^bsub>x x'\<^esub> (g (l1 x))"
      using \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close> \<open>g (l1 x) \<le>\<^bsub>R2 (l1 x) x'\<^esub> _\<close> by blast
    moreover have "... \<le>\<^bsub>L2 x (r1 x')\<^esub> r2\<^bsub>x x'\<^esub> (g x')"
      using mono_r2 \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close> \<open>g (l1 x) \<le>\<^bsub>R2 (l1 x) x'\<^esub> g x'\<close> by blast
    ultimately show "f x \<le>\<^bsub>L2 x (r1 x')\<^esub> r2\<^bsub>x x'\<^esub> (g x')"
      using trans_L2 \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close> by blast
  qed
qed

lemma Galois_if_Dep_Fun_Rel_rel_GaloisI:
  assumes mono_l1: "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and half_galois_prop_right1: "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and L2_unit_le2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and ge_L2_r2_le1: "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
  and "in_codom (\<le>\<^bsub>R\<^esub>) g"
  and rel_f_g: "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g"
proof (intro GaloisI left_relI)
  show "in_codom (\<le>\<^bsub>R\<^esub>) g" by fact
  fix x1 x2 assume "x1 \<le>\<^bsub>L1\<^esub> x2"
  with mono_l1 half_galois_prop_right1 have "x1 \<^bsub>L1\<^esub>\<lessapprox> l1 x2"
    by (intro g1.Galois_left_if_left_relI) auto
  with rel_f_g have "f x1 \<^bsub>L2 x1 (l1 x2)\<^esub>\<lessapprox> g (l1 x2)" by blast
  then have "in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) (g (l1 x2))"
    "f x1 \<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub> r2\<^bsub>x1 (l1 x2)\<^esub> (g (l1 x2))" by auto
  with L2_unit_le2 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "f x1 \<le>\<^bsub>L2 x1 x2\<^esub> r2\<^bsub>x1 (l1 x2)\<^esub> (g (l1 x2))" by blast
  with ge_L2_r2_le1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> \<open>in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) (g (l1 x2))\<close>
    have "f x1 \<le>\<^bsub>L2 x1 x2\<^esub> r2\<^bsub>x2 (l1 x2)\<^esub> (g (l1 x2))" by blast
  then show "f x1 \<le>\<^bsub>L2 x1 x2\<^esub> r g x2" by simp
qed

end


paragraph \<open>Reflexive Relator\<close>

context transport_Refl_Rel_Dep_Fun_Rel_rel
begin

lemma Dep_Fun_Rel_rel_Galois_if_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x x' y'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x (l1 x)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x x'\<^esub> y')"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "f \<^bsub>L\<^esub>\<lessapprox> g"
  shows "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro t.Dep_Fun_Rel_rel_Galois_if_GaloisI t.GaloisI)
  (auto elim!: galois_rel.GaloisE in_codomE
    simp only: left_rel_eq_Refl_Rel right_rel_eq_Refl_Rel)

lemma Galois_if_Dep_Fun_Rel_rel_GaloisI:
  assumes "(t.R \<Rrightarrow>\<^sub>m t.L) r"
  and "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
  and "in_field (\<le>\<^bsub>L\<^esub>) f"
  and "in_field (\<le>\<^bsub>R\<^esub>) g"
  and "([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g"
  using assms unfolding left_rel_eq_Refl_Rel right_rel_eq_Refl_Rel
  by (intro t.Galois_Refl_RelI t.Galois_if_Dep_Fun_Rel_rel_GaloisI)
  (auto elim!: in_fieldE)

corollary Galois_iff_Dep_Fun_Rel_rel_GaloisI:
  assumes "(t.R \<Rrightarrow>\<^sub>m t.L) r"
  and "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
  and "\<And>x x' y'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x (l1 x)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x x'\<^esub> y')"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "in_field (\<le>\<^bsub>L\<^esub>) f"
  and "in_field (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro iffI Dep_Fun_Rel_rel_Galois_if_GaloisI)
  (auto intro!: Galois_if_Dep_Fun_Rel_rel_GaloisI)

corollary Galois_iff_Dep_Fun_Rel_rel_Galois_if_galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
  and "\<And>x x' y'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x (l1 x)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x x'\<^esub> y')"
  and "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<le>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x1)\<^esub> y')"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "in_field (\<le>\<^bsub>L\<^esub>) f"
  and "in_field (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro Galois_iff_Dep_Fun_Rel_rel_GaloisI
    t.mono_wrt_rel_rightI t.mono_wrt_rel_right_mono_asm_if_mono_wrt_relI)
  auto

lemma Galois_iff_Dep_Fun_Rel_rel_Galois_if_galois_connectionI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and mono_r2_1: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
  and mono_r2_2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and mono_r2_2': "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow>
    ([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
  and trans_L2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "in_field (\<le>\<^bsub>L\<^esub>) f"
  and "in_field (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
proof -
  from mono_r2_1 have "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub> y')"
    using trans_L2 by blast
  moreover from mono_r2_2 have "\<And>x x' y'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>) y' \<Longrightarrow>
    (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x (l1 x)\<^esub> y') \<le> (\<ge>\<^bsub>L2 x (r1 x')\<^esub>) (r2\<^bsub>x x'\<^esub> y')"
    using trans_L2 by blast
  moreover from mono_r2_2' have "\<And>x1 x2 y'. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y' \<Longrightarrow>
    (\<le>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub> y') \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>) (r2\<^bsub>x1 (l1 x1)\<^esub> y')"
    using trans_L2 by blast
  ultimately show ?thesis using assms
    by (intro Galois_iff_Dep_Fun_Rel_rel_Galois_if_galois_connectionI) auto
qed

lemma Galois_iff_Dep_Fun_Rel_rel_Galois_if_mono_if_galois_connectionI:
  assumes galois_conn1: "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and L2_le_unit2: "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and mono_r2: "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "in_field (\<le>\<^bsub>L\<^esub>) f"
  and "in_field (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
proof -
  have "([in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x2)\<^esub>) (r2\<^bsub>x2 (l1 x2)\<^esub>)"
    if "x1 \<le>\<^bsub>L1\<^esub> x2" for x1 x2
  proof (intro Dep_Fun_Rel_predI)
    from galois_conn1 refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "l1 x2 \<le>\<^bsub>R1\<^esub> l1 x2" "x2 \<^bsub>L1\<^esub>\<lessapprox> l1 x2"
      by (blast intro: g1.Galois_left_if_left_relI)+
    fix y' assume "in_codom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y'"
    with Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_r2 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>] \<open>l1 x2 \<le>\<^bsub>R1\<^esub> l1 x2\<close>]
      have "r2\<^bsub>x1 (l1 x2)\<^esub> y' \<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub> r2\<^bsub>x2 (l1 x2)\<^esub> y'"
      using \<open>x2 \<^bsub>L1\<^esub>\<lessapprox> l1 x2\<close> by (auto dest: in_field_if_in_codom)
    with L2_le_unit2 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> show "r2\<^bsub>x1 (l1 x2)\<^esub> y' \<le>\<^bsub>L2 x1 x2\<^esub> r2\<^bsub>x2 (l1 x2)\<^esub> y'"
      by blast
  qed
  moreover have "([in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)) (r2\<^bsub>x1 (l1 x1)\<^esub>) (r2\<^bsub>x1 (l1 x2)\<^esub>)"
    if "x1 \<le>\<^bsub>L1\<^esub> x2" for x1 x2
  proof (intro Dep_Fun_Rel_predI)
    from galois_conn1 refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>
      have "x1 \<le>\<^bsub>L1\<^esub> x1" "l1 x1 \<le>\<^bsub>R1\<^esub> l1 x2" "x1 \<^bsub>L1\<^esub>\<lessapprox> l1 x1"
      by (blast intro: g1.Galois_left_if_left_relI)+
    fix y' assume "in_dom (\<le>\<^bsub>R2 (l1 x1) (l1 x2)\<^esub>) y'"
    with Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_r2 \<open>x1 \<le>\<^bsub>L1\<^esub> x1\<close>] \<open>l1 x1 \<le>\<^bsub>R1\<^esub> l1 x2\<close>]
      have "r2\<^bsub>x1 (l1 x1)\<^esub> y' \<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub> r2\<^bsub>x1 (l1 x2)\<^esub> y'"
      using \<open>x1 \<^bsub>L1\<^esub>\<lessapprox> l1 x1\<close> by (auto dest: in_field_if_in_dom)
    with L2_le_unit2 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> show "r2\<^bsub>x1 (l1 x1)\<^esub> y' \<le>\<^bsub>L2 x1 x2\<^esub> r2\<^bsub>x1 (l1 x2)\<^esub> y'"
      by blast
  qed
  moreover have "([in_dom (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x (l1 x)\<^esub>) (r2\<^bsub>x x'\<^esub>)"
    if "x \<^bsub>L1\<^esub>\<lessapprox> x'" for x x'
  proof -
    from galois_conn1 refl_L1 \<open>x \<^bsub>L1\<^esub>\<lessapprox> x'\<close>
      have "x \<le>\<^bsub>L1\<^esub> x" "l1 x \<le>\<^bsub>R1\<^esub> x'" "x \<^bsub>L1\<^esub>\<lessapprox> l1 x"
      by (auto intro!: g1.half_galois_prop_leftD g1.Galois_left_if_left_relI)
    with Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_r2 \<open>x \<le>\<^bsub>L1\<^esub> x\<close>] \<open>l1 x \<le>\<^bsub>R1\<^esub> x'\<close>]
      show ?thesis by blast
  qed
  ultimately show ?thesis using assms
    by (intro Galois_iff_Dep_Fun_Rel_rel_Galois_if_galois_connectionI')
    (auto intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom)
qed

lemma Galois_iff_Dep_Fun_Rel_rel_Galois_if_mono_if_galois_connectionI':
  assumes galois_conn1: "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and mono_L2: "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
  and antimono_L2:
    "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x1 \<le>\<^bsub>L1\<^esub> x2 \<and> x3 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2)] \<Rrightarrow>\<^sub>m (\<ge>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "in_field (\<le>\<^bsub>L\<^esub>) f"
  and "in_field (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
proof -
  have "(\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)" and "(\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
    if "x1 \<le>\<^bsub>L1\<^esub> x2" for x1 x2
  proof -
    from refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "x1 \<le>\<^bsub>L1\<^esub> x1" by blast
    with dep_mono_wrt_relD[OF dep_mono_wrt_predD[OF mono_L2] \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>]
      show "(\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)" by auto
    from galois_conn1 refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2"
      by (blast intro: g1.rel_unit_if_reflexive_on_if_half_galois_prop_right_if_mono_wrt_rel)
    with refl_L1 have "\<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2" by blast
    with dep_mono_wrt_relD[OF dep_mono_wrt_predD[OF antimono_L2] \<open>x2 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2\<close>]
      show "(\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)" using \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> by auto
  qed
  then show ?thesis using assms
    by (intro Galois_iff_Dep_Fun_Rel_rel_Galois_if_mono_if_galois_connectionI)
    auto
qed

corollary Galois_eq_Dep_Fun_Rel_rel_Galois_restrict_if_mono_if_galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
  and "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | (x1 \<le>\<^bsub>L1\<^esub> x2 \<and> x3 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2)] \<Rrightarrow>\<^sub>m (\<ge>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_field (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_field (\<le>\<^bsub>R\<^esub>)\<^esub>"
  using assms by (intro ext iffI restrict_leftI restrict_rightI
    iffD1[OF Galois_iff_Dep_Fun_Rel_rel_Galois_if_mono_if_galois_connectionI'])
  (auto elim!: GaloisE intro!:
    iffD2[OF Galois_iff_Dep_Fun_Rel_rel_Galois_if_mono_if_galois_connectionI'])

lemma Galois_iff_Dep_Fun_Rel_rel_Galois_if_galois_equivalenceI:
  assumes galois_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and refl_L1: "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and mono_L2: "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "in_field (\<le>\<^bsub>L\<^esub>) f"
  and "in_field (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
proof -
  interpret flip1 : galois R1 L1 r1 l1
    rewrites "flip1.counit \<equiv> \<eta>\<^sub>1" by (simp only: g1.flip_counit_eq_unit)
  have "(\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)" and "(\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
    if "x1 \<le>\<^bsub>L1\<^esub> x2" for x1 x2
  proof -
    from refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "x1 \<le>\<^bsub>L1\<^esub> x1" by blast
    with dep_mono_wrt_relD[OF dep_mono_wrt_predD[OF mono_L2] \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>]
      show "(\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)" by auto
    from galois_equiv1 refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "\<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> x2"
      by (intro flip1.counit_rel_if_reflexive_on_if_half_galois_prop_left_if_mono_wrt_rel)
      blast+
    from galois_equiv1 refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "x1 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2"
      by (fastforce intro: g1.rel_unit_if_left_rel_if_mono_wrt_relI)
    with dep_mono_wrt_relD[OF dep_mono_wrt_predD[OF mono_L2] \<open>\<eta>\<^sub>1 x2 \<le>\<^bsub>L1\<^esub> x2\<close>]
      show "(\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)" by auto
  qed
  then show ?thesis using assms
    by (intro Galois_iff_Dep_Fun_Rel_rel_Galois_if_mono_if_galois_connectionI)
    auto
qed

lemma Galois_iff_Dep_Fun_Rel_rel_Galois_mono_assm_leftI:
  assumes mono_L2: "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and refl_L1: "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  shows "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
proof (intro dep_mono_wrt_predI dep_mono_wrt_relI rel_if_if_impI)
  fix x1 x2 x3 assume "x1 \<le>\<^bsub>L1\<^esub> x2" "x2 \<le>\<^bsub>L1\<^esub> x3"
  with refl_L1 have "x1 \<ge>\<^bsub>L1\<^esub> x1" by blast
  from Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_L2 \<open>x1 \<ge>\<^bsub>L1\<^esub> x1\<close>]
    \<open>x2 \<le>\<^bsub>L1\<^esub> x3\<close>] \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>
    show "(\<le>\<^bsub>L2 x1 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x3\<^esub>)" by blast
qed

corollary Galois_iff_Dep_Fun_Rel_rel_Galois_if_galois_equivalenceI':
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "in_field (\<le>\<^bsub>L\<^esub>) f"
  and "in_field (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>)) f g"
  using assms by (intro Galois_iff_Dep_Fun_Rel_rel_Galois_if_galois_equivalenceI
    Galois_iff_Dep_Fun_Rel_rel_Galois_mono_assm_leftI)
  auto

theorem Galois_eq_Dep_Fun_Rel_rel_Galois_restrict_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_field (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_field (\<le>\<^bsub>R\<^esub>)\<^esub>"
  using assms by (intro ext iffI restrict_leftI restrict_rightI
    iffD1[OF Galois_iff_Dep_Fun_Rel_rel_Galois_if_galois_equivalenceI'])
  (auto elim!: GaloisE intro!:
    iffD2[OF Galois_iff_Dep_Fun_Rel_rel_Galois_if_galois_equivalenceI'])

corollary Galois_eq_Dep_Fun_Rel_rel_Galois_restrict_if_order_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)" "transitive (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>R2 (l1 x) x'\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2 x (r1 x')\<^esub>)) (r2\<^bsub>x x'\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ([x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)] \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_field (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_field (\<le>\<^bsub>R\<^esub>)\<^esub>"
  using assms by (intro
    Galois_eq_Dep_Fun_Rel_rel_Galois_restrict_if_galois_equivalenceI
    g1.galois_equivalence_left_right_if_transitive_if_order_equivalence
    reflexive_on_in_field_if_transitive_if_rel_equivalence_on)
  auto

end


paragraph \<open>Non-Dependent Function Relator\<close>

context transport_Refl_Rel_Fun_Rel_rel
begin

lemma Fun_Rel_rel_Galois_if_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1" and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "((\<le>\<^bsub>L1\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) (r2)"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "f \<^bsub>L\<^esub>\<lessapprox> g"
  shows "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
  using assms by (intro rdfr.Dep_Fun_Rel_rel_Galois_if_GaloisI) auto

lemma Galois_if_Fun_Rel_rel_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "in_field (\<le>\<^bsub>L\<^esub>) f"
  and "in_field (\<le>\<^bsub>R\<^esub>) g"
  and "((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g"
  using assms
  by (intro rdfr.Galois_if_Dep_Fun_Rel_rel_GaloisI rdfr.t.mono_wrt_rel_rightI)
  auto

corollary Galois_iff_Fun_Rel_rel_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  and "in_field (\<le>\<^bsub>L\<^esub>) f"
  and "in_field (\<le>\<^bsub>R\<^esub>) g"
  shows "f \<^bsub>L\<^esub>\<lessapprox> g \<longleftrightarrow> ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>)) f g"
  using assms by (intro iffI Fun_Rel_rel_Galois_if_GaloisI)
  (auto intro!: Galois_if_Fun_Rel_rel_GaloisI)

theorem Galois_eq_Fun_Rel_rel_Galois_restrictI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) r2"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_field (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_field (\<le>\<^bsub>R\<^esub>)\<^esub>"
  using assms by (intro ext iffI restrict_leftI restrict_rightI
    iffD1[OF Galois_iff_Fun_Rel_rel_GaloisI])
  (auto elim!: rdfr.GaloisE intro!: iffD2[OF Galois_iff_Fun_Rel_rel_GaloisI])

end


end