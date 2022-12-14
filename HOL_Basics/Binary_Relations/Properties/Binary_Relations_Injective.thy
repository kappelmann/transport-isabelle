\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Injective\<close>
theory Binary_Relations_Injective
  imports
    Binary_Relation_Functions
    Lattices_Syntax
begin

consts rel_injective_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  rel_injective_on_pred \<equiv> "rel_injective_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_injective_on_pred P R \<equiv> \<forall>x x' y. P x \<and> P x' \<and> R x y \<and> R x' y \<longrightarrow> x = x'"
end

lemma rel_injective_onI [intro]:
  assumes "\<And>x x' y. P x \<Longrightarrow> P x' \<Longrightarrow> R x y \<Longrightarrow> R x' y \<Longrightarrow> x = x'"
  shows "rel_injective_on P R"
  unfolding rel_injective_on_pred_def using assms by blast

lemma rel_injective_onD:
  assumes "rel_injective_on P R"
  and "P x" "P x'"
  and "R x y" "R x' y"
  shows "x = x'"
  using assms unfolding rel_injective_on_pred_def by blast

definition "rel_injective (R :: 'a \<Rightarrow> _) \<equiv> rel_injective_on (\<top> :: 'a \<Rightarrow> bool) R"

lemma rel_injective_eq_rel_injective_on:
  "rel_injective (R :: 'a \<Rightarrow> _) = rel_injective_on (\<top> :: 'a \<Rightarrow> bool) R"
  unfolding rel_injective_def ..

lemma rel_injectiveI [intro]:
  assumes "\<And>x x' y. R x y \<Longrightarrow> R x' y \<Longrightarrow> x = x'"
  shows "rel_injective R"
  unfolding rel_injective_eq_rel_injective_on using assms by blast

lemma rel_injectiveD:
  assumes "rel_injective R"
  and "R x y" "R x' y"
  shows "x = x'"
  using assms unfolding rel_injective_eq_rel_injective_on
  by (auto dest: rel_injective_onD)

lemma rel_injective_on_if_rel_injective:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "rel_injective R"
  shows "rel_injective_on P R"
  using assms by (blast dest: rel_injectiveD)

lemma rel_injective_if_rel_injective_on_in_dom:
  assumes "rel_injective_on (in_dom R) R"
  shows "rel_injective R"
  using assms by (blast dest: rel_injective_onD)

corollary rel_injective_on_in_dom_iff_rel_injective [simp]:
  "rel_injective_on (in_dom R) R \<longleftrightarrow> rel_injective R"
  using rel_injective_if_rel_injective_on_in_dom rel_injective_on_if_rel_injective
  by blast


end