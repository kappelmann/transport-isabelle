\<^marker>\<open>creator "Kevin Kappelmann"\<close>
paragraph \<open>Surjective\<close>
theory Binary_Relations_Surjective
  imports
    Binary_Relation_Functions
    HOL_Syntax_Bundles_Lattices
begin

consts rel_surjective_at :: "'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"

overloading
  rel_surjective_at_pred \<equiv> "rel_surjective_at :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_surjective_at_pred P R \<equiv> \<forall>y. P y \<longrightarrow> in_codom R y"
end

lemma rel_surjective_atI [intro]:
  assumes "\<And>y. P y \<Longrightarrow> in_codom R y"
  shows "rel_surjective_at P R"
  unfolding rel_surjective_at_pred_def using assms by blast

lemma rel_surjective_atE [elim]:
  assumes "rel_surjective_at P R"
  and "P y"
  obtains x where "R x y"
  using assms unfolding rel_surjective_at_pred_def by blast

lemma in_codom_if_rel_surjective_at_on:
  assumes "rel_surjective_at P R"
  and "P y"
  shows "in_codom R y"
  using assms by blast

definition "rel_surjective (R :: _ \<Rightarrow> 'a \<Rightarrow> _) \<equiv> rel_surjective_at (\<top> :: 'a \<Rightarrow> bool) R"

lemma rel_surjective_eq_rel_surjective_at:
  "rel_surjective (R :: _ \<Rightarrow> 'a \<Rightarrow> _) = rel_surjective_at (\<top> :: 'a \<Rightarrow> bool) R"
  unfolding rel_surjective_def ..

lemma rel_surjectiveI:
  assumes "\<And>y. in_codom R y"
  shows "rel_surjective R"
  unfolding rel_surjective_eq_rel_surjective_at using assms by (intro rel_surjective_atI)

lemma rel_surjectiveE:
  assumes "rel_surjective R"
  obtains x where "R x y"
  using assms unfolding rel_surjective_eq_rel_surjective_at
  by (blast intro: top1I)

lemma in_codom_if_rel_surjective_at:
  assumes "rel_surjective R"
  shows "in_codom R y"
  using assms by (blast elim: rel_surjectiveE)

lemma rel_surjective_at_if_surjective:
  fixes P :: "'a \<Rightarrow> bool" and R :: "_ \<Rightarrow> 'a \<Rightarrow> _"
  assumes "rel_surjective R"
  shows "rel_surjective_at P R"
  using assms by (intro rel_surjective_atI) (blast dest: in_codom_if_rel_surjective_at)


end