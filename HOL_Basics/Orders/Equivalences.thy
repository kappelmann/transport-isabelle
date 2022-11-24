\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Equivalences\<close>
theory Equivalences
  imports
    Partial_Equivalences
begin

definition "equivalence_on P R \<equiv> partial_equivalence_on P R \<and> reflexive_on P R"

lemma equivalence_onI [intro]:
  assumes "partial_equivalence_on P R"
  and "reflexive_on P R"
  shows "equivalence_on P R"
  unfolding equivalence_on_def using assms by blast

lemma equivalence_onE [elim]:
  assumes "equivalence_on P R"
  obtains "partial_equivalence_on P R" "reflexive_on P R"
  using assms unfolding equivalence_on_def by blast

definition "equivalence (R :: 'a \<Rightarrow> _) \<equiv> equivalence_on (\<top> :: 'a \<Rightarrow> bool) R"

lemma equivalence_eq_equivalence_on:
  "equivalence (R :: 'a \<Rightarrow> _) = equivalence_on (\<top> :: 'a \<Rightarrow> bool) R"
  unfolding equivalence_def ..

lemma equivalenceI [intro]:
  assumes "partial_equivalence R"
  and "reflexive R"
  shows "equivalence R"
  unfolding equivalence_eq_equivalence_on using assms
  by (intro equivalence_onI partial_equivalence_on_if_partial_equivalence
    reflexive_on_if_reflexive)

lemma equivalenceE [elim]:
  assumes "equivalence R"
  obtains "partial_equivalence R" "reflexive R"
  using assms unfolding equivalence_eq_equivalence_on
  by (elim equivalence_onE)
  (simp only: partial_equivalence_eq_partial_equivalence_on
    reflexive_eq_reflexive_on)

lemma equivalence_on_if_equivalence:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "equivalence R"
  shows "equivalence_on P R"
  using assms by (elim equivalenceE)
  (intro equivalence_onI partial_equivalence_on_if_partial_equivalence
    reflexive_on_if_reflexive)


subsubsection \<open>Instantiations\<close>

lemma equivalence_eq: "equivalence (=)"
  using partial_equivalence_eq reflexive_eq by (rule equivalenceI)

lemma equivalence_top: "equivalence \<top>"
  using partial_equivalence_top reflexive_top by (rule equivalenceI)

end