theory Lifting_Set_Extensions
  imports
    Lifting_Sets
    Isabelle_Set.Set_Extension
begin

context set_extension
begin

  (* for A Rep inj *)
abbreviation "abs \<equiv> Abs"
abbreviation "rep \<equiv> Rep"
abbreviation "rel \<equiv> Iso_Rel B abs"

lemma z_property: "z_property rel"
  using z_property_Iso_Rel .

lemma bijection: "bijection B abs_image abs rep"
  apply (rule bijectionI)
  apply (rule ElementD)
  apply (rule Dep_fun_typeE[OF Abs_type])
  apply (fact ElementI)
  apply (rule ElementD)
  apply (rule Dep_fun_typeE[OF Rep_type])
    apply (fact ElementI)
  apply (rule inverse_onI)
    apply (rule Rep_Abs_inv)
  apply (rule inverse_onI)
    apply (fact Abs_Rep_inv)
  done

lemma injective: "LBinary_Relations.injective rel"
  using bijection
  by (intro injective_Iso_Rel_if_injective_on injective_on_if_bijection)

lemma "Eq_rep rel = Eq_Rel B"
  using Eq_rep_Iso_Rel_eq_if_bijection bijection .

lemma lifting_triple: "lifting_triple rel abs rep"
  using lifting_triple_Iso_Rel_if_bijection bijection .

end


end