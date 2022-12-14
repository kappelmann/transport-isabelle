\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transport using Identity\<close>
theory Transport_Identity
  imports
    Transport_Bijections
begin

locale transport_id =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

sublocale tbij? : transport_bijection L L id id
  by (intro transport_bijection.intro) auto

end

locale transport_reflexive_on_in_field_id =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes reflexive_on_in_field: "reflexive_on (in_field L) L"
begin

sublocale trefl_bij? : transport_reflexive_on_in_field_bijection L L id id
  using reflexive_on_in_field by unfold_locales auto

end

locale transport_preorder_on_in_field_id =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes preorder_on_in_field: "preorder_on (in_field L) L"
begin

sublocale tpre_bij? : transport_preorder_on_in_field_bijection L L id id
  using preorder_on_in_field by unfold_locales auto

end

locale transport_partial_equivalence_id =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes partial_equivalence: "partial_equivalence L"
begin

sublocale tper_bij? : transport_partial_equivalence_bijection L L id id
  using partial_equivalence by unfold_locales auto

end

interpretation transport_eq_restrict_id :
  transport_eq_restrict_bijection P P id id for  P :: "'a \<Rightarrow> bool"
  using bijection_on_self_id by (unfold_locales) auto

interpretation transport_eq_id : transport_eq_bijection id id
  using bijection_on_self_id by (unfold_locales) auto

end
