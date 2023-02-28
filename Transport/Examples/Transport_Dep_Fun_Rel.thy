\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Transport for Dependent Function Relator\<close>
theory Transport_Dep_Fun_Rel
  imports
    Transport_PER
    Transport_Syntax
    "HOL-Library.IArray"
begin

paragraph \<open>Summary\<close>
text \<open>Dependent function relator examples from the Transport paper.
Refer to the paper for more details.\<close>


context
  includes galois_rel_syntax transport_syntax
begin
interpretation transport L R l r for L R l r .

abbreviation "Zpos \<equiv> ((=\<^bsub>(\<le>)(0 :: int)\<^esub>) :: int \<Rightarrow> _)"

lemma Zpos_per [per_intro]: "(Zpos \<equiv>\<^bsub>PER\<^esub> (=)) nat int"
  by fastforce

lemma sub_parametric [transport_parametric]:
  "([i _ \<Colon> Zpos] \<Rrightarrow> [j _ \<Colon> Zpos | j \<le> i] \<Rrightarrow> Zpos) (-) (-)"
  by fastforce

transport_term nat_sub :: "nat \<Rightarrow> nat \<Rightarrow> nat" where x = "(-) :: int \<Rightarrow> _"
  and L = "[i _ \<Colon> Zpos] \<Rrightarrow> [j _ \<Colon> Zpos | j \<le> i] \<Rrightarrow> Zpos"
  and R = "[n _ \<Colon> (=)] \<Rrightarrow> [m _ \<Colon> (=) | m \<le> n] \<Rrightarrow> (=)"
  (*fastforce discharges the remaining side-conditions*)
  by transport_term_prover fastforce+

text \<open>Note: as of now, @{command transport_term} does not rewrite the
Galois relator of dependent function relators.\<close>
thm nat_sub_related'
thm nat_sub_app_eq


abbreviation "LRel \<equiv> list_all2"
abbreviation "IARel \<equiv> rel_iarray"

lemma transp_eq_transitive: "transp = transitive"
  by (auto intro: transpI dest: transpD)
lemma symp_eq_symmetric: "symp = symmetric"
  by (auto intro: sympI dest: sympD symmetricD)

lemma [per_intro]:
  assumes "partial_equivalence_rel R"
  shows "(LRel R \<equiv>\<^bsub>PER\<^esub> IARel R) IArray.IArray IArray.list_of"
  using assms by (fastforce simp flip: transp_eq_transitive symp_eq_symmetric
    intro: list.rel_transp list.rel_symp iarray.rel_transp iarray.rel_symp
    elim: iarray.rel_cases)+

lemma [transport_parametric]:
  "([xs _ \<Colon> LRel R] \<Rrightarrow> [i _ \<Colon> (=) | i < length xs] \<Rrightarrow> R) (!) (!)"
  by (fastforce simp: list_all2_lengthD list_all2_nthD2)

context
  fixes R :: "'a \<Rightarrow> _" assumes [per_intro]: "partial_equivalence_rel R"
begin

interpretation Rper : transport_partial_equivalence_rel_id R
  by unfold_locales per_prover
declare Rper.partial_equivalence_rel_equivalence [per_intro]

transport_term iarray_index where x = "(!) :: 'a list \<Rightarrow> _"
  and L = "([xs _ \<Colon> LRel R] \<Rrightarrow> [i _ \<Colon> (=) | i < length xs] \<Rrightarrow> R)"
  and R = "([xs _ \<Colon> IARel R] \<Rrightarrow> [i _ \<Colon> (=) | i < IArray.length xs] \<Rrightarrow> R)"
  by transport_term_prover
  (*fastforce discharges the remaining side-conditions*)
  (fastforce simp: list_all2_lengthD elim: iarray.rel_cases)+

end
end

end