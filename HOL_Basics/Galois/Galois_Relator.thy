\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Relator For Galois Connections\<close>
theory Galois_Relator
  imports
    Galois_Property
begin

locale galois_rel = orders L R
  for L :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and R :: "'c \<Rightarrow> 'd \<Rightarrow> bool"
  and r :: "'d \<Rightarrow> 'b"
begin

text \<open>Morally speaking, the Galois relator characterises when two terms
\<^term>\<open>x :: 'a\<close> and \<^term>\<open>y :: 'b\<close> are "similar".\<close>

definition "Galois x y \<equiv> in_codom (\<le>\<^bsub>R\<^esub>) y \<and> x \<le>\<^bsub>L\<^esub> r y"

notation Galois (infix "\<^bsub>L\<^esub>\<lessapprox>" 50)

abbreviation (input) "ge_Galois \<equiv> (\<^bsub>L\<^esub>\<lessapprox>)\<inverse>"
notation ge_Galois (infix "\<greaterapprox>\<^bsub>L\<^esub>" 50)

lemma GaloisI [intro]:
  assumes "in_codom (\<le>\<^bsub>R\<^esub>) y"
  and "x \<le>\<^bsub>L\<^esub> r y"
  shows "x \<^bsub>L\<^esub>\<lessapprox> y"
  unfolding Galois_def using assms by blast

lemma GaloisE [elim]:
  assumes "x \<^bsub>L\<^esub>\<lessapprox> y"
  obtains "in_codom (\<le>\<^bsub>R\<^esub>) y" "x \<le>\<^bsub>L\<^esub> r y"
  using assms unfolding Galois_def by blast

corollary in_dom_if_Galois:
  assumes "x \<^bsub>L\<^esub>\<lessapprox> y"
  shows "in_dom (\<le>\<^bsub>L\<^esub>) x"
  using assms by blast

corollary Galois_iff_in_codom_and_left_rel_right:
  "x \<^bsub>L\<^esub>\<lessapprox> y \<longleftrightarrow> in_codom (\<le>\<^bsub>R\<^esub>) y \<and> x \<le>\<^bsub>L\<^esub> r y"
  by blast

lemma Galois_restrict_left_eq_Galois_left_restrict_left:
  "(\<^bsub>L\<^esub>\<lessapprox>)\<restriction>\<^bsub>P :: 'a \<Rightarrow> bool\<^esub> = galois_rel.Galois (\<le>\<^bsub>L\<^esub>)\<restriction>\<^bsub>P\<^esub> (\<le>\<^bsub>R\<^esub>) r"
  by (intro ext iffI galois_rel.GaloisI restrict_leftI)
  (auto elim: galois_rel.GaloisE)

lemma Galois_restrict_right_eq_Galois_right_restrict_right:
  "(\<^bsub>L\<^esub>\<lessapprox>)\<upharpoonleft>\<^bsub>P :: 'd \<Rightarrow> bool\<^esub> = galois_rel.Galois (\<le>\<^bsub>L\<^esub>) (\<le>\<^bsub>R\<^esub>)\<upharpoonleft>\<^bsub>P\<^esub> r"
  by (intro ext iffI galois_rel.GaloisI restrict_rightI)
  (auto elim!: galois_rel.GaloisE restrict_rightE)

end

context galois_prop
begin

sublocale galois_rel L R r .

interpretation flip_inv : galois_rel "(\<ge>\<^bsub>R\<^esub>)" "(\<ge>\<^bsub>L\<^esub>)" l .

abbreviation "flip_inv_Galois \<equiv> flip_inv.Galois"
notation flip_inv_Galois (infix "\<^bsub>R\<^esub>\<greaterapprox>" 50)

abbreviation (input) "flip_inv_ge_Galois \<equiv> flip_inv.ge_Galois"
notation flip_inv_ge_Galois (infix "\<lessapprox>\<^bsub>R\<^esub>" 50)

lemma Galois_if_left_right_rel_if_in_dom_if_half_galois_prop_right:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "in_dom (\<le>\<^bsub>L\<^esub>) x"
  and "l x \<le>\<^bsub>R\<^esub> y"
  shows "x \<^bsub>L\<^esub>\<lessapprox> y"
  using assms by (intro GaloisI) auto

lemma half_galois_prop_left_GaloisE:
  assumes "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<^bsub>L\<^esub>\<lessapprox> y"
  obtains "in_dom (\<le>\<^bsub>L\<^esub>) x" "l x \<le>\<^bsub>R\<^esub> y"
  using assms by blast

corollary Galois_iff_in_dom_and_left_right_rel_if_galois_prop:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "x \<^bsub>L\<^esub>\<lessapprox> y \<longleftrightarrow> in_dom (\<le>\<^bsub>L\<^esub>) x \<and> l x \<le>\<^bsub>R\<^esub> y"
  using assms
    Galois_if_left_right_rel_if_in_dom_if_half_galois_prop_right
    half_galois_prop_left_GaloisE
  by fastforce

lemma rel_inv_Galois_eq_flip_Galois_rel_inv_if_galois_prop [simp]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "(\<greaterapprox>\<^bsub>L\<^esub>) = (\<^bsub>R\<^esub>\<greaterapprox>)" \<comment>\<open>Note that @{term "(\<^bsub>R\<^esub>\<greaterapprox>) = galois_rel.Galois (\<ge>\<^bsub>R\<^esub>) (\<ge>\<^bsub>L\<^esub>) l"}\<close>
proof (intro ext)
  fix y x
  have "y \<greaterapprox>\<^bsub>L\<^esub> x \<longleftrightarrow> x \<^bsub>L\<^esub>\<lessapprox> y" by simp
  also have "... \<longleftrightarrow> in_codom (\<le>\<^bsub>R\<^esub>) y \<and> x \<le>\<^bsub>L\<^esub> r y"
    by (fact Galois_iff_in_codom_and_left_rel_right)
  also from assms have "... \<longleftrightarrow> in_codom (\<ge>\<^bsub>L\<^esub>) x \<and> y \<ge>\<^bsub>R\<^esub> l x" by blast
  also have "... \<longleftrightarrow> y \<^bsub>R\<^esub>\<greaterapprox> x"
    by (fact flip_inv.Galois_iff_in_codom_and_left_rel_right[symmetric])
  finally show "y \<greaterapprox>\<^bsub>L\<^esub> x \<longleftrightarrow> y \<^bsub>R\<^esub>\<greaterapprox> x" .
qed

corollary flip_Galois_rel_inv_iff_Galois_if_galois_prop [iff]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "y \<^bsub>R\<^esub>\<greaterapprox> x \<longleftrightarrow> x \<^bsub>L\<^esub>\<lessapprox> y"
  using assms by blast

corollary inv_flip_Galois_rel_inv_eq_Galois_if_galois_prop [simp]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "(\<lessapprox>\<^bsub>R\<^esub>) = (\<^bsub>L\<^esub>\<lessapprox>)" \<comment>\<open>Note that @{term "(\<lessapprox>\<^bsub>R\<^esub>) = (galois_rel.Galois (\<ge>\<^bsub>R\<^esub>) (\<ge>\<^bsub>L\<^esub>) l)\<inverse>"}\<close>
  using assms by (subst rel_inv_eq_iff_eq[symmetric]) simp

end

context galois
begin

context
begin

interpretation flip : galois R L r l .

abbreviation "flip_Galois \<equiv> flip.Galois"
notation flip_Galois (infix "\<^bsub>R\<^esub>\<lessapprox>" 50)

abbreviation (input) "flip_ge_Galois \<equiv> flip.ge_Galois"
notation flip_ge_Galois (infix "\<greaterapprox>\<^bsub>R\<^esub>" 50)

abbreviation "flip_flip_inv_Galois \<equiv> flip.flip_inv_Galois"
notation flip_flip_inv_Galois (infix "\<^bsub>L\<^esub>\<greaterapprox>" 50)

abbreviation (input) "flip_flip_inv_ge_Galois \<equiv> flip.flip_inv_ge_Galois"
notation flip_flip_inv_ge_Galois (infix "\<lessapprox>\<^bsub>L\<^esub>" 50)

lemma Galois_left_if_left_relI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<le>\<^bsub>L\<^esub> x'"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x'"
  using assms
  by (intro Galois_if_left_right_rel_if_in_dom_if_half_galois_prop_right) auto

corollary Galois_left_if_reflexive_on_if_half_galois_prop_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  and "P x"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x"
  using assms by (intro Galois_left_if_left_relI) auto

lemma Galois_left_if_in_codom_if_inflationary_onI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "inflationary_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
  and "in_codom (\<le>\<^bsub>L\<^esub>) x"
  and "P x"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x"
  using assms by (intro GaloisI) (auto elim!: in_codomE)

lemma Galois_left_if_in_codom_if_inflationary_on_in_codomI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "inflationary_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  and "in_codom (\<le>\<^bsub>L\<^esub>) x"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x"
  using assms by (auto intro!: Galois_left_if_in_codom_if_inflationary_onI)

lemma Galois_left_if_left_rel_if_inflationary_on_in_fieldI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "inflationary_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  and "x \<le>\<^bsub>L\<^esub> x"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x"
  using assms by (auto intro!: Galois_left_if_in_codom_if_inflationary_onI)

lemma right_Galois_if_right_relI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "y \<le>\<^bsub>R\<^esub> y'"
  shows "r y \<^bsub>L\<^esub>\<lessapprox> y'"
  using assms by (intro GaloisI) auto

corollary right_Galois_if_reflexive_onI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "reflexive_on P (\<le>\<^bsub>R\<^esub>)"
  and "P y"
  shows "r y \<^bsub>L\<^esub>\<lessapprox> y"
  using assms by (intro right_Galois_if_right_relI) auto

lemma Galois_if_right_rel_if_GaloisI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "transitive (\<le>\<^bsub>L\<^esub>)"
  and "x \<^bsub>L\<^esub>\<lessapprox> y"
  and "y \<le>\<^bsub>R\<^esub> z"
  shows "x \<^bsub>L\<^esub>\<lessapprox> z"
  using assms by (intro GaloisI) auto

lemma Galois_if_Galois_if_left_relI:
  assumes "transitive (\<le>\<^bsub>L\<^esub>)"
  and "x \<le>\<^bsub>L\<^esub> y"
  and "y \<^bsub>L\<^esub>\<lessapprox> z"
  shows "x \<^bsub>L\<^esub>\<lessapprox> z"
  using assms by (intro GaloisI) auto

lemma left_rel_if_Galois_if_GaloisI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L\<^esub>)) r l"
  and "transitive (\<le>\<^bsub>L\<^esub>)"
  and "x \<^bsub>L\<^esub>\<lessapprox> y"
  and "y \<^bsub>R\<^esub>\<lessapprox> z"
  shows "x \<le>\<^bsub>L\<^esub> z"
  using assms by blast

lemma Dep_Fun_Rel_Galois_left_right_if_mono_wrt_rel [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>R\<^esub>\<lessapprox>)) l r"
  using assms by blast

lemma Galois_rel_inv_eq_Galois_if_in_codom_eq_in_dom_if_symmetric:
  assumes "symmetric (\<le>\<^bsub>L\<^esub>)"
  and "in_codom (\<le>\<^bsub>R\<^esub>) = in_dom (\<le>\<^bsub>R\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<greaterapprox>) = (\<^bsub>L\<^esub>\<lessapprox>)" \<comment>\<open>Note that @{term "(\<^bsub>L\<^esub>\<greaterapprox>) = galois_rel.Galois (\<ge>\<^bsub>L\<^esub>) (\<ge>\<^bsub>R\<^esub>) r"}\<close>
  using assms by (intro ext iffI)
  (auto elim!: galois_rel.GaloisE intro!: galois_rel.GaloisI)

end

interpretation flip : galois R L r l .

lemma inv_flip_Galois_eq_Galois_if_symmetric_if_in_codom_eq_in_dom_if_galois_prop:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "in_codom (\<le>\<^bsub>L\<^esub>) = in_dom (\<le>\<^bsub>L\<^esub>)"
  and "symmetric (\<le>\<^bsub>R\<^esub>)"
  shows "(\<greaterapprox>\<^bsub>R\<^esub>) = (\<^bsub>L\<^esub>\<lessapprox>)" \<comment>\<open>Note that @{term "(\<greaterapprox>\<^bsub>R\<^esub>) = (galois_rel.Galois (\<le>\<^bsub>R\<^esub>) (\<le>\<^bsub>L\<^esub>) l)\<inverse>"}\<close>
  using assms
  by (simp only: inv_flip_Galois_rel_inv_eq_Galois_if_galois_prop
    flip: flip.Galois_rel_inv_eq_Galois_if_in_codom_eq_in_dom_if_symmetric)

interpretation gp : galois_prop "(\<^bsub>L\<^esub>\<lessapprox>)" "(\<^bsub>R\<^esub>\<lessapprox>)" l l .

lemma half_galois_prop_left_Galois_left_if_half_galois_prop_leftI [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<^sub>h\<unlhd> (\<^bsub>R\<^esub>\<lessapprox>)) l l"
  using assms by fast

lemma half_galois_prop_right_Galois_left_if_half_galois_prop_rightI [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<unlhd>\<^sub>h (\<^bsub>R\<^esub>\<lessapprox>)) l l"
  using assms by fast

corollary galois_prop_Galois_left_if_galois_prop [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<unlhd> (\<^bsub>R\<^esub>\<lessapprox>)) l l"
  using assms by blast

end


end