From mathcomp Require Import all_ssreflect. (* from mathcomp *)
From mathcomp Require Import finmap. (* from finmap *)
From mathcomp Require Import mathcomp_extra classical_sets. (* from analysis *)
Require Import mathcomp_extra graph complete_graph S_suspension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.

Local Open Scope fset_scope.
(* Local Open Scope classical_set_scope. *)

Section neighbourhood.
Variable G : llugraph.

(*
Definition classical_openNeighbourhood (v : `V G) :=
  [set w | exists e, e \in `E G /\ v \in `d(e) /\ w \in `d(e) ].
*)

Definition open_neighbourhood (v : `V G) := [fset w : `V G | [exists e, (e \in `E G) && (`d(e) == [fset v; w]) ]].

Definition closed_neighbourhood (v : `V G) := v |` open_neighbourhood v.
(* = [fset v] `|` open_neighbourhood v. *)


(* If G has a loop, this lemma does not hold. *)
Lemma open_neighbourhood_not_closed (v : `V G) :
  v \notin open_neighbourhood v.
Proof.
rewrite !inE /= fsetUid.
apply/existsP => -[] e /eqP /(congr1 (fun A => #|` A |)).
by rewrite boundary_card2 cardfs1.
Qed.

Lemma closed_neighbourhoodDorigin (v : `V G) :
  closed_neighbourhood v `\ v = open_neighbourhood v.
Proof.
rewrite/ closed_neighbourhood.
apply fsetU1K.
apply open_neighbourhood_not_closed.
Qed.

(*
Lemma open_neighbourhood_not_closed (v : `V G) :
  v \notin open_neighbourhood v.
Proof.
rewrite !inE /=.
apply/existsP.
case=> e /eqP.
rewrite fsetUid.
About congr1.
About size.
(*
move/(congr1 (size \o val) ) => /=.
move/(congr1 (fun A : {fset `V G} => size A) ).
 *)
move/(congr1 (fun A => #|` A | )).
by rewrite boundary_card2 cardfs1.
Qed.
*)

Lemma open_neighbourhood_eachother (u v : `V G) :
  u \in open_neighbourhood v <-> v \in open_neighbourhood u.
Proof.
by split; rewrite /open_neighbourhood !inE /= fsetUC.
Qed.


Definition is_overcomplete_graph G :=
  forall v w : `V G, v != w -> exists e : `E G, `d e = [fset v; w].

Lemma complete_is_overcomplete :
  is_complete_graph G -> is_overcomplete_graph G.
Proof.
by case.
(*
exact: proj2.
*)
Qed.

Lemma neighbourhood_overcomplete :
  is_overcomplete_graph G <-> forall v : `V G, #|` closed_neighbourhood v | = #| `V G |.
Proof.
rewrite -cardfsT.
split.
  move=> icg v.
  apply/eq_cardfs/eqP.
  rewrite eqEfsubset fsubsetT /=.
  apply/fsubsetP => u _.
  rewrite !inE.
  have[-> //|vu /=]:= eqVneq v u.
  apply/existsP.
  have /(_ v u vu):= icg.
  by case=> e /eqP ?; exists e.
move=> + v w /[1!eq_sym] wv => /(_ v) /esym /eq_leq H.
have:= eqEfcard (closed_neighbourhood v) [fset: `V G].
rewrite fsubsetT H /= eq_sym eqEfcard => /andP [] + _.
move=> /fsubsetP /(_ w).
rewrite !inE (negPf wv) => /(_ erefl) /=.
by move=> /existsP [] e /eqP ? ; exists e.
Qed.

End neighbourhood.

Section neighbourhood_lemmas.

Variable G : llugraph.
Variable is_connected_graph : llugraph -> Prop.

Lemma induced_matching_edgeC (S : {fset (`E G)}) (e f g : `E G) (u v : `V G) :
S \in induced_matching G ->
e \in S ->
f \in S ->
e != f ->
u \in `d e -> v \in `d f -> `d g != [fset u; v].
Proof.
move=> /induced_matchingP /(_ e f) /[apply] /[apply] /[apply] H ude vdf.
apply/eqP => dguv.
by case: (H g) => /fdisjointP => [/(_ u ude)|/(_ v vdf)]; rewrite dguv !inE eqxx // orbT.
Qed.

Arguments induced_matching_edgeC {S}.

(* Lemma 1.4 in https://arxiv.org/pdf/2503.01500 *)
Local Lemma nindmatch_gt1_ (e : `E G) (v : `V G) :
  e \in sval (exists_nindmatch G) ->
  1 < nindmatch G ->
  v \in `d e ->
  ~ is_independent_set (~` open_neighbourhood v).
Proof.
case: (exists_nindmatch G) => I /= indI -> eI.
rewrite (cardfsD1 e I) eI /= -[ltnLHS]addn0 ltn_add2l cardfs_gt0.
case/fset0Pn => f + vde.
rewrite in_fsetD1 eq_sym => /andP [] ef fI.
move/is_independent_setP.
have:= boundary_exists2 f => -[] x [] y [] xdf [] ydf xy.
move/(_ x y).
apply.
- rewrite !inE /= andbT.
  apply/existsP => -[] g.
  exact/negP/(induced_matching_edgeC e f g v x indI) => //.
- rewrite !inE /= andbT.
  apply/existsP => -[] g.
  exact/negP/(induced_matching_edgeC e f g v y indI) => //.
exists f.
apply/eqP.
rewrite -in_biboundary biboundary_fsetMDdiag !inE /=.
by rewrite in_fset_diag xdf ydf xy.
Qed.


Definition is_coindependent_set (S : {fset `V G}) := is_independent_set (~` S).

Lemma open_neighbourhood_is_coindependent (v : `V G) :
  is_coindependent_set (closed_neighbourhood v) ->
  is_coindependent_set (open_neighbourhood v).
Proof.
rewrite /is_coindependent_set /is_independent_set.
rewrite -!negb_exists.
apply: contraNN.
case/existsP => e /fsubsetP H.
case/boolP: (v \in `d e) => vde; last first.
  apply/existsP; exists e; apply/fsubsetP => u /[dup] ude /H.
  rewrite !inE /= !andbT.
  apply: contraNN.
  case/orP => // /eqP uv.
  by have:= vde; rewrite -uv ude.
exfalso.
have[[u1 u2]/= [u12 deu]]:= boundary_sig2 e.
have:= vde.
rewrite deu in_fset2 => vu12.
wlog: u1 u2 u12 deu vu12 / v == u1.
  case/orP: vu12 => vu => [/(_ u1 u2) | /(_ u2 u1)].
    by apply => //; rewrite vu.
  rewrite eq_sym fsetUC.
  by apply => //; rewrite vu.
move/eqP => vu1.
have:= H u2.
rewrite deu !inE /= andbT eqxx orbT.
move/(_ erefl)/negP; apply.
apply/existsP.
exists e.
by rewrite deu vu1.
Qed.

Lemma nindmatch_gt1 (e : `E G) (v : `V G) :
  e \in sval (exists_nindmatch G) ->
  1 < nindmatch G ->
  v \in `d e ->
  ~ is_independent_set (~` closed_neighbourhood v).
Proof.
move=> eI nind vde.
have:= nindmatch_gt1_ eI nind vde.
exact/contra_not/open_neighbourhood_is_coindependent.
Qed.

Lemma nindmatch_gt1' (v : `V G) :
  1 < nindmatch G ->
  v \in VofESet (sval (exists_nindmatch G)) ->
   ~ is_independent_set (~` closed_neighbourhood v).
Proof.
move=> nindgt1 /bigfcupP [] /= S /[!andbT] /imfsetP [] /= e eI -> vde.
exact: (nindmatch_gt1 eI).
Qed.



End neighbourhood_lemmas.
