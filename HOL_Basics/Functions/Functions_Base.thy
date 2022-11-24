\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Functions_Base
  imports HOL.HOL
begin

subsection \<open>Basic Functions\<close>

definition "id x \<equiv> x"

lemma id_eq_self [simp]: "id x = x"
  unfolding id_def ..

definition "comp f g x \<equiv> f (g x)"

bundle comp_syntax begin notation comp (infixl "\<circ>" 55) end
bundle no_comp_syntax begin no_notation comp (infixl "\<circ>" 55) end
unbundle comp_syntax

lemma comp_eq [simp]: "(f \<circ> g) x = f (g x)"
  unfolding comp_def ..

lemma id_comp_eq [simp]: "id \<circ> f = f"
  by (rule ext) simp

lemma comp_id_eq [simp]: "f \<circ> id = f"
  by (rule ext) simp

definition "dep_fun_map f g h x \<equiv> g x (f x) (h (f x))"

lemma dep_fun_map_eq [simp]: "dep_fun_map f g h x = g x (f x) (h (f x))"
  unfolding dep_fun_map_def ..

definition "fun_map f g h \<equiv> dep_fun_map f (\<lambda>_ _. g) h"

lemma fun_map_eq_comp [simp]: "fun_map f g h = g \<circ> h \<circ> f"
  unfolding fun_map_def dep_fun_map_eq by fastforce

lemma fun_map_eq [simp]: "fun_map f g h x = g (h (f x))"
  unfolding fun_map_eq_comp by simp

lemma fun_map_id_eq_comp [simp]: "fun_map id = (\<circ>)"
  by (intro ext) simp

lemma fun_map_id_eq_comp' [simp]: "fun_map f id h = h \<circ> f"
  by (intro ext) simp



end