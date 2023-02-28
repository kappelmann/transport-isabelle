\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Transport for HOL Type Definitions\<close>
theory Transport_Typedef_Base
  imports
    Transport.Transport_Bijections
    HOL.Typedef
begin

overloading
  eq_restrict_set \<equiv> "eq_restrict :: 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
begin
  definition "eq_restrict_set (S :: 'a set) \<equiv> ((=\<^bsub>\<lambda>x. x \<in> S\<^esub>) :: 'a \<Rightarrow> _)"
end

lemma eq_restrict_set_eq_eq_restrict_pred [simp]:
  "((=\<^bsub>S :: 'a set\<^esub>) :: 'a \<Rightarrow> _) = (=\<^bsub>\<lambda>x. x \<in> S\<^esub>)"
  unfolding eq_restrict_set_def by simp

lemma eq_restrict_set_iff_eq_restrict_pred [iff]:
  "(x :: 'a) =\<^bsub>(S :: 'a set)\<^esub> y \<longleftrightarrow> x =\<^bsub>(\<lambda>x. x \<in> S)\<^esub> y"
  by simp

overloading
  restrict_left_set \<equiv> "restrict_left :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a set) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
begin
  definition "restrict_left_set (R :: 'a \<Rightarrow> _) (S :: 'a set) \<equiv> R\<restriction>\<^bsub>\<lambda>x. x \<in> S\<^esub>"
end

lemma restrict_left_set_eq_restrict_left_pred [simp]:
  "(R\<restriction>\<^bsub>S :: 'a set\<^esub> :: 'a \<Rightarrow> _) = R\<restriction>\<^bsub>\<lambda>x. x \<in> S\<^esub>"
  unfolding restrict_left_set_def by simp

lemma restrict_left_set_iff_restrict_left_pred [iff]:
  "(R\<restriction>\<^bsub>S :: 'a set\<^esub> :: 'a \<Rightarrow> _) x y \<longleftrightarrow> R\<restriction>\<^bsub>\<lambda>x. x \<in> S\<^esub> x y"
  by simp

context type_definition
begin

abbreviation (input) "L :: 'a \<Rightarrow> 'a \<Rightarrow> bool \<equiv> (=\<^bsub>A\<^esub>)"
abbreviation (input) "R :: 'b \<Rightarrow> 'b \<Rightarrow> bool \<equiv> (=)"

sublocale transport? :
  transport_eq_restrict_bijection "\<lambda>x. x \<in> A" "\<top> :: 'b \<Rightarrow> bool" Abs Rep
  rewrites "(=\<^bsub>\<lambda>(x :: 'a). x \<in> A\<^esub>) \<equiv> L"
  and "(=\<^bsub>\<top> :: 'b \<Rightarrow> bool\<^esub>) \<equiv> R"
  and "(galois_rel.Galois (=) (=) Rep)\<restriction>\<^bsub>\<lambda>x. x \<in> A\<^esub>\<upharpoonleft>\<^bsub>\<top> :: 'b \<Rightarrow> bool\<^esub> \<equiv>
    (galois_rel.Galois (=) (=) Rep)\<restriction>\<^bsub>A\<^esub>"
  using Rep Abs_inverse Rep_inverse
  by (intro transport_eq_restrict_bijection.intro bijection_onI)
  (auto simp: restrict_right_eq)

interpretation galois L R Abs Rep .

lemma Galois_Rep_self: "Rep y \<^bsub>L\<^esub>\<lessapprox> y"
  using Rep by (intro GaloisI) auto

end


end