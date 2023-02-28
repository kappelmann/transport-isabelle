theory Transport_Syntax
  imports
    Transport.Transport
begin

abbreviation "Galois_infix x L R r y \<equiv> galois_rel.Galois L R r x y"
abbreviation (input) "ge_Galois R r L \<equiv> galois_rel.ge_Galois L R r"
abbreviation (input) "ge_Galois_infix y R r L x \<equiv> ge_Galois R r L y x"

bundle galois_rel_syntax
begin
  notation galois_rel.Galois ("'((\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>(_) (_)\<^esub>)')")
  notation Galois_infix ("(_) (\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>(_) (_)\<^esub>) (_)" [51,51,51,51,51] 50)
  notation ge_Galois ("'((\<^bsub>(_) (_)\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>)')")
  notation ge_Galois_infix ("(_) (\<^bsub>(_) (_)\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>) (_)" [51,51,51,51,51] 50)
end
bundle no_galois_rel_syntax
begin
  no_notation galois_rel.Galois ("'((\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>(_) (_)\<^esub>)')")
  no_notation Galois_infix ("(_) (\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>(_) (_)\<^esub>) (_)" [51,51,51,51,51] 50)
  no_notation ge_Galois ("'((\<^bsub>(_) (_)\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>)')")
  no_notation ge_Galois_infix ("(_) (\<^bsub>(_) (_)\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>) (_)" [51,51,51,51,51] 50)
end

abbreviation "transport_DFR_l \<equiv> transport_Dep_Fun_Rel.l"
abbreviation "transport_FR_l \<equiv> transport_Fun_Rel.l"

bundle transport_Dep_Fun_Rel_syntax begin
syntax
  "_transport_FR_l" :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>
    ('a \<Rightarrow> 'd)" ("(_) \<rightarrow>t (_)" [41, 40] 40)
  "_transport_DFR_l" :: "idt \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>
    ('a \<Rightarrow> 'd)" ("[_/ : / _] \<rightarrow>t (_)" [41, 41, 40] 40)
end
bundle no_transport_Dep_Fun_Rel_syntax begin
no_syntax
  "_transport_FR_l" :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>
    ('a \<Rightarrow> 'd)" ("(_) \<rightarrow>t (_)" [41, 40] 40)
  "_transport_DFR_l" :: "idt \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow>
    ('a \<Rightarrow> 'd)" ("[_/ : / _] \<rightarrow>t (_)" [41, 41, 40] 40)
end
unbundle transport_Dep_Fun_Rel_syntax
translations
  "f \<rightarrow>t g" \<rightleftharpoons> "CONST transport_FR_l f g"
  "[x : f] \<rightarrow>t g" \<rightleftharpoons> "CONST transport_DFR_l f (\<lambda>x. g)"

bundle transport_syntax
begin
  unbundle transport_Dep_Fun_Rel_syntax
  notation transport.preorder_equivalence (infix "\<equiv>\<^bsub>pre\<^esub>" 50)
  notation transport.partial_equivalence_rel_equivalence (infix "\<equiv>\<^bsub>PER\<^esub>" 50)
end
bundle no_transport_syntax
begin
  unbundle no_transport_Dep_Fun_Rel_syntax
  no_notation transport.preorder_equivalence (infix "\<equiv>\<^bsub>pre\<^esub>" 50)
  no_notation transport.partial_equivalence_rel_equivalence (infix "\<equiv>\<^bsub>PER\<^esub>" 50)
end


end