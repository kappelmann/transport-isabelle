\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transport For Compositions\<close>
theory Transport_Compositions
  imports
    Transport_Compositions_Agree
    Transport_Compositions_Generic
begin

paragraph \<open>Summary\<close>
text \<open>We provide two ways to compose transportable components:
a slightly intricate, generic one in @{locale "transport_comp"} and
another straightforward but less general one in @{locale "transport_comp_agree"}.
As a special case from the latter, we obtain @{locale "transport_comp_same"},
which includes the cases most prominently covered in the literature.

Refer to the paper
"Transport via Partial Galois Connections and Equivalences" by Kevin Kappelmann.
for more details.\<close>

end