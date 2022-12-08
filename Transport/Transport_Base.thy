\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Basic Setup\<close>
theory Transport_Base
  imports
    HOL_Basics.Galois_Equivalences
    HOL_Basics.Galois_Relator
begin

locale transport = galois L R l r
  for L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and l :: "'a \<Rightarrow> 'b"
  and r :: "'b \<Rightarrow> 'a"
begin

subsubsection \<open>Galois Connections on Orders\<close>

definition "preorder_galois_connection \<equiv>
  ((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r
  \<and> preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)
  \<and> preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"

notation transport.preorder_galois_connection (infix "\<stileturn>\<^bsub>pre\<^esub>" 50)

lemma preorder_galois_connectionI [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding preorder_galois_connection_def using assms by blast

lemma preorder_galois_connectionE [elim]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  obtains "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r" "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
    "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  using assms unfolding preorder_galois_connection_def by blast

context
begin

interpretation t : transport S T f g for S T f g .

lemma rel_inv_preorder_galois_connection_eq_preorder_galois_connection_rel_inv [simp]:
  "((\<le>\<^bsub>R\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>L\<^esub>))\<inverse> = ((\<ge>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<ge>\<^bsub>R\<^esub>))"
  by (intro ext) (auto intro!: t.preorder_galois_connectionI)

end

corollary preorder_galois_connection_rel_inv_iff_preorder_galois_connection [iff]:
  "((\<ge>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<ge>\<^bsub>R\<^esub>)) l r \<longleftrightarrow> ((\<le>\<^bsub>R\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>L\<^esub>)) r l"
  by (simp flip:
    rel_inv_preorder_galois_connection_eq_preorder_galois_connection_rel_inv)

definition "partial_equivalence_galois_connection \<equiv>
  ((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r
  \<and> partial_equivalence (\<le>\<^bsub>L\<^esub>)
  \<and> partial_equivalence (\<le>\<^bsub>R\<^esub>)"

notation transport.partial_equivalence_galois_connection (infix "\<stileturn>\<^bsub>PER\<^esub>" 50)

lemma partial_equivalence_galois_connectionI [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "partial_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and "partial_equivalence_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding partial_equivalence_galois_connection_def using assms by blast

lemma partial_equivalence_galois_connectionE [elim]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  obtains "((\<le>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r" "symmetric (\<le>\<^bsub>L\<^esub>)" "symmetric (\<le>\<^bsub>R\<^esub>)"
  using assms unfolding partial_equivalence_galois_connection_def by blast

context
begin

interpretation t : transport S T f g for S T f g .

lemma rel_inv_partial_equivalence_galois_connection_eq_partial_equivalence_galois_connection_rel_inv
  [simp]: "((\<le>\<^bsub>R\<^esub>) \<stileturn>\<^bsub>PER\<^esub> (\<le>\<^bsub>L\<^esub>))\<inverse> = ((\<ge>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>PER\<^esub> (\<ge>\<^bsub>R\<^esub>))"
  by (intro ext) blast

end

corollary partial_equivalence_galois_connection_rel_inv_iff_partial_equivalence_galois_connection
  [iff]: "((\<ge>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>PER\<^esub> (\<ge>\<^bsub>R\<^esub>)) l r \<longleftrightarrow> ((\<le>\<^bsub>R\<^esub>) \<stileturn>\<^bsub>PER\<^esub> (\<le>\<^bsub>L\<^esub>)) r l"
  by (simp flip:
    rel_inv_partial_equivalence_galois_connection_eq_partial_equivalence_galois_connection_rel_inv)

lemma Galois_comp_rel_inv_Galois_eq_left_if_partial_equivalence_galois_connection:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<circ>\<circ> (\<greaterapprox>\<^bsub>L\<^esub>)) = (\<le>\<^bsub>L\<^esub>)"
proof (intro ext iffI)
  fix x x' assume "((\<^bsub>L\<^esub>\<lessapprox>) \<circ>\<circ> (\<greaterapprox>\<^bsub>L\<^esub>)) x x'"
  then obtain y where "x \<le>\<^bsub>L\<^esub> r y" "r y \<ge>\<^bsub>L\<^esub> x'" by blast
  moreover with assms have "r y \<le>\<^bsub>L\<^esub> x'" by (blast dest: symmetricD)
  ultimately show "x \<le>\<^bsub>L\<^esub> x'" using assms by blast
next
  fix x x' assume "x \<le>\<^bsub>L\<^esub> x'"
  with assms have "x \<^bsub>L\<^esub>\<lessapprox> l x'" "x' \<^bsub>L\<^esub>\<lessapprox> l x'"
    by (blast intro: Galois_left_if_left_relI)+
  moreover with assms have "l x' \<lessapprox>\<^bsub>L\<^esub> x'"
    by (subst Galois_rel_inv_eq_Galois_if_in_codom_eq_in_dom_if_symmetric)
    (blast intro: in_codom_eq_in_dom_if_partial_equivalence)+
  ultimately show "((\<^bsub>L\<^esub>\<lessapprox>) \<circ>\<circ> (\<greaterapprox>\<^bsub>L\<^esub>)) x x'" by blast
qed


subsubsection \<open>Equivalences on Orders\<close>

definition "preorder_equivalence \<equiv>
  ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r
  \<and> preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)
  \<and> preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"

notation transport.preorder_equivalence (infix "\<equiv>\<^bsub>pre\<^esub>" 50)

lemma preorder_equivalence_if_galois_equivalenceI [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  and "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding preorder_equivalence_def using assms by blast

lemma preorder_equivalence_if_order_equivalenceI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  and "transitive (\<le>\<^bsub>L\<^esub>)"
  and "transitive (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding preorder_equivalence_def using assms
  by (blast intro: reflexive_on_in_field_if_transitive_if_rel_equivalence_on
    dest: galois_equivalence_left_right_if_transitive_if_order_equivalence)

lemma preorder_equivalence_galois_equivalenceE [elim]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  obtains "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r" "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
    "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  using assms unfolding preorder_equivalence_def by blast

lemma preorder_equivalence_order_equivalenceE:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  obtains "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r" "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
    "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  using assms by (blast intro:
    order_equivalence_if_reflexive_on_in_field_if_galois_equivalence)

context
begin

interpretation t : transport S T f g for S T f g .

lemma rel_inv_preorder_equivalence_eq_preorder_equivalence [simp]:
  "((\<le>\<^bsub>R\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>L\<^esub>))\<inverse> = ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>))"
  by (intro ext) blast

end

corollary preorder_equivalence_right_left_iff_preorder_equivalence_left_right:
  "((\<le>\<^bsub>R\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>L\<^esub>)) r l \<longleftrightarrow> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  by (simp flip: rel_inv_preorder_equivalence_eq_preorder_equivalence)

lemma preorder_equivalence_rel_inv_eq_preorder_equivalence [simp]:
  "((\<ge>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<ge>\<^bsub>R\<^esub>)) = ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>))"
  by (intro ext iffI)
  (auto intro!: transport.preorder_equivalence_if_galois_equivalenceI
    elim!: transport.preorder_equivalence_galois_equivalenceE)

definition "partial_equivalence_equivalence \<equiv>
  ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r
  \<and> partial_equivalence (\<le>\<^bsub>L\<^esub>)
  \<and> partial_equivalence (\<le>\<^bsub>R\<^esub>)"

notation transport.partial_equivalence_equivalence (infix "\<equiv>\<^bsub>PER\<^esub>" 50)

lemma partial_equivalence_equivalence_if_galois_equivalenceI [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  and "partial_equivalence (\<le>\<^bsub>L\<^esub>)"
  and "partial_equivalence (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding partial_equivalence_equivalence_def using assms by blast

lemma partial_equivalence_equivalence_if_order_equivalenceI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  and "partial_equivalence (\<le>\<^bsub>L\<^esub>)"
  and "partial_equivalence (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding partial_equivalence_equivalence_def using assms
  by (blast dest: galois_equivalence_left_right_if_transitive_if_order_equivalence)

lemma partial_equivalence_equivalenceE [elim]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  obtains "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r" "symmetric (\<le>\<^bsub>L\<^esub>)" "symmetric (\<le>\<^bsub>R\<^esub>)"
  using assms unfolding partial_equivalence_equivalence_def by blast

context
begin

interpretation t : transport S T f g for S T f g .

lemma rel_inv_partial_equivalence_equivalence_eq_partial_equivalence_equivalence [simp]:
  "((\<le>\<^bsub>R\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>L\<^esub>))\<inverse> = ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>))"
  by (intro ext) blast

end

corollary partial_equivalence_equivalence_right_left_iff_partial_equivalence_equivalence_left_right:
  "((\<le>\<^bsub>R\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>L\<^esub>)) r l \<longleftrightarrow> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  by (simp flip:
    rel_inv_partial_equivalence_equivalence_eq_partial_equivalence_equivalence)

lemma partial_equivalence_equivalence_rel_inv_eq_partial_equivalence_equivalence
  [simp]: "((\<ge>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<ge>\<^bsub>R\<^esub>)) = ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>))"
  by (intro ext iffI)
  (auto intro!: transport.partial_equivalence_equivalence_if_galois_equivalenceI
    elim!: transport.partial_equivalence_equivalenceE
      transport.preorder_equivalence_galois_equivalenceE
      preorder_on_in_fieldE)

end


end