subsection \<open>Lifting With Galois Connections\<close>
theory Lifting_Galois_Connections
  imports
    Galois_Relator
    Binary_Relations_Intersection
    (* Lifting_Triples *)
begin

lemma galois_property:
  fixes Pl :: "'a \<Rightarrow> bool" and Pr :: "'b \<Rightarrow> bool" and l :: "'a \<Rightarrow> 'b"
  assumes bij: "bijection_on Pl Pr l r"
  shows "galois_property (Eq_Rel\<restriction>Pl) (Eq_Rel\<restriction>Pr) l r"
proof (rule galois_propertyI)
  fix x y
  have "(Eq_Rel\<restriction>Pl) x (r y) \<longleftrightarrow> Pl x \<and> x = r y"
    by (intro iffI) (blast intro: restrictI Eq_RelI elim: restrictE Eq_RelE)+
  also have "... \<longleftrightarrow> Pr (l x) \<and> l x = y"
  proof (intro iffI conjI)
    presume "Pl x"
    with bij show "Pr (l x)" by (elim bijection_on_prop_right)
    presume "x = r y"
    (* x = r l x
    l r y = y
      x = r l r y
    l x = l r l x *)
    (* l x = y *)

    then have "l x = l (r y)" by (rule arg_cong)
    (* Pl x \<and> x = r y *)
  qed
 (* (auto intro: bijection_on_prop_right app_app_eq_self_if_bijection_on'[symmetric]) *)
  (* thm app_app_eq_self_if_bijection_on'[symmetric] *)
    (* (auto intro: bijection_on_prop_right bijection_on_prop_left *)
      (* simp: app_app_eq_self_if_bijection_on app_app_eq_self_if_bijection_on) *)
    (* by (intro iffI) (blast intro: restrictI Eq_RelI elim: restrictE Eq_RelE)+ *)
  (* finally show "(Eq_Rel\<restriction>Pl) x (r y) \<longleftrightarrow> (Eq_Rel\<restriction>Pr) (l x) y" . *)
qed

(* lemma lifting_triple_Eq_Rel_id: "lifting_triple (Eq_Rel A) id id"
  using bijection_id
  by (subst Eq_Rel_eq_Iso_Rel) (intro lifting_triple_Iso_Rel_if_bijection) *)


lemma lifting_triple_monotone_Eq_rep_Eq_abs_abs:
  assumes "lifting_triple R abs rep"
  shows "monotone (Eq_rep R) (Eq_abs R) abs"
  using assms
  by (intro dep_monotoneI lifting_triple_Eq_abs_abs_abs_if_Eq_rep)

lemma lifting_triple_monotone_Eq_abs_Eq_rep_rep:
  assumes "lifting_triple R abs rep"
  shows "monotone (Eq_abs R) (Eq_rep R) rep"
  using assms
  by (intro dep_monotoneI lifting_triple_Eq_rep_rep_rep_if_Eq_abs)

lemma lifting_triple_Eq_abs_abs_if_Eq_rep_rep:
  assumes lift_trip: "lifting_triple R abs rep"
  and in_codom: "in_codom (Eq_abs R) y"
  and Eq_rep: "Eq_rep R x (rep y)"
  shows "Eq_abs R (abs x) y"
proof -
  from lift_trip have "transitive (Eq_abs R)"
    by (intro transitive_Eq_abs_if_z_property z_property_if_lifting_triple)
  from lift_trip Eq_rep have Eq_abs_abs_abs_rep: "(Eq_abs R) (abs x) (abs (rep y))"
    by (intro lifting_triple_Eq_abs_abs_abs_if_Eq_rep)
  from in_codom have "in_codom R y" by (rule in_codom_if_in_codom_Eq_abs)
  with lift_trip have "(Eq_abs R) (abs (rep y)) y"
    by (rule lifting_triple_Eq_abs_abs_rep_self_if_in_codom)
  with \<open>transitive (Eq_abs R)\<close> Eq_abs_abs_abs_rep show "(Eq_abs R) (abs x) y"
    by (rule transitiveD)
qed

lemma lifting_triple_Eq_rep_rep_if_Eq_abs_abs:
  assumes lift_trip: "lifting_triple R abs rep"
  and in_dom: "in_dom (Eq_rep R) x"
  and Eq_abs: "Eq_abs R (abs x) y"
  shows "Eq_rep R x (rep y)"
proof -
  from lift_trip have "transitive (Eq_rep R)"
    by (intro transitive_Eq_rep_if_z_property z_property_if_lifting_triple)
  from in_dom have "in_dom R x" by (rule in_dom_if_in_dom_Eq_rep)
  with lift_trip have Eq_rep_rep_abs: "(Eq_rep R) x (rep (abs x))"
    by (rule lifting_triple_Eq_rep_rep_abs_self_if_in_dom)
  from lift_trip Eq_abs have "(Eq_rep R) (rep (abs x)) (rep y)"
    by (intro lifting_triple_Eq_rep_rep_rep_if_Eq_abs)
  with \<open>transitive (Eq_rep R)\<close> Eq_rep_rep_abs show "(Eq_rep R) x (rep y)"
    by (blast intro: transitiveD)
qed

lemma galois_property_if_lifting_triple:
  assumes "lifting_triple R abs rep"
  shows "galois_property (Eq_rep R) (Eq_abs R) abs rep"
  using assms
  (* by (intro galois_propertyI)
    (blast intro: lifting_triple_Eq_abs_abs_if_Eq_rep_rep lifting_triple_Eq_rep_rep_if_Eq_abs_abs) *)

lemma galois_connection_if_lifting_triple:
  assumes "lifting_triple R abs rep"
  shows "galois_connection (Eq_rep R) (Eq_abs R) abs rep"
  using assms
  by (intro galois_connectionI lifting_triple_monotone_Eq_rep_Eq_abs_abs
    lifting_triple_monotone_Eq_abs_Eq_rep_rep galois_property_if_lifting_triple)


end