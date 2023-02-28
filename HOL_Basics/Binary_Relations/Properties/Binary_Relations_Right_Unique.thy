\<^marker>\<open>creator "Kevin Kappelmann"\<close>
paragraph \<open>Right Unique\<close>
theory Binary_Relations_Right_Unique
  imports
    Binary_Relation_Functions
    HOL_Syntax_Bundles_Lattices
begin

consts right_unique_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  right_unique_on_pred \<equiv> "right_unique_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "right_unique_on_pred P R \<equiv> \<forall>x y y'. P x \<and> R x y \<and> R x y' \<longrightarrow> y = y'"
end

lemma right_unique_onI [intro]:
  assumes "\<And>x y y'. P x \<Longrightarrow> R x y \<Longrightarrow> R x y' \<Longrightarrow> y = y'"
  shows "right_unique_on P R"
  using assms unfolding right_unique_on_pred_def by blast

lemma right_unique_onD:
  assumes "right_unique_on P R"
  and "P x"
  and "R x y" "R x y'"
  shows "y = y'"
  using assms unfolding right_unique_on_pred_def by blast

definition "right_unique (R :: 'a \<Rightarrow> _) \<equiv> right_unique_on (\<top> :: 'a \<Rightarrow> bool) R"

lemma right_unique_eq_right_unique_on:
  "right_unique (R :: 'a \<Rightarrow> _) = right_unique_on (\<top> :: 'a \<Rightarrow> bool) R"
  unfolding right_unique_def ..

lemma right_uniqueI [intro]:
  assumes "\<And>x y y'. R x y \<Longrightarrow> R x y' \<Longrightarrow> y = y'"
  shows "right_unique R"
  unfolding right_unique_eq_right_unique_on using assms by blast

lemma right_uniqueD:
  assumes "right_unique R"
  and "R x y" "R x y'"
  shows "y = y'"
  using assms unfolding right_unique_eq_right_unique_on
  by (auto dest: right_unique_onD)

lemma right_unique_on_if_right_unique:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "right_unique R"
  shows "right_unique_on P R"
  using assms by (blast dest: right_uniqueD)

lemma right_unique_if_right_unique_on_in_dom:
  assumes "right_unique_on (in_dom R) R"
  shows "right_unique R"
  using assms by (blast dest: right_unique_onD)

corollary right_unique_on_in_dom_iff_right_unique [iff]:
  "right_unique_on (in_dom R) R \<longleftrightarrow> right_unique R"
  using right_unique_if_right_unique_on_in_dom right_unique_on_if_right_unique
  by blast

paragraph \<open>Instantiations\<close>

lemma right_unique_eq: "right_unique (=)"
  by (rule right_uniqueI) blast


end