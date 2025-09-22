From mathcomp Require Import all_ssreflect. (* from mathcomp *)
From mathcomp Require Import finmap multiset. (* from finmap *)
From mathcomp Require Import mathcomp_extra classical_sets. (* from analysis *)
Require Import mathcomp_extra graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.

Local Open Scope fset_scope.

Section biboundary.
Variable G : llugraph.

Definition biboundary (e : `E G) :=
  let: exist (a, b) _ := cardfs2_sig (boundary_card2 e) in
  [fset (a, b); (b, a)].

Lemma biboundaryE (e : `E G) (a b : `V G) :
 `d e = [fset a; b] -> biboundary e = [fset (a, b); (b, a)].
Proof.
move=> deab.
have ab: a != b.
  apply/eqP; move:deab => /[swap] -> /(congr1 (size \o val)) /=.
  by rewrite boundary_card2 fsetUid cardfs1.
move: deab.
rewrite /biboundary /=.
case: cardfs2_sig => [] [u v] /= [uv] -> /fsetP uvab.
apply/fsetP=> -[x y].
rewrite !inE !xpair_eqE.
wlog: u v a b uv ab uvab / (u == a); last first.
  move: uvab => /[swap] /eqP -> /(_ b).
  by rewrite !inE (eq_sym b a) (negPf ab) eqxx /= => /eqP ->.
case/boolP: (u == a).
  by move /[swap] /[apply]; apply.
move=> ua.
move: (uvab) => /(_ u).
rewrite !inE eqxx (negPf ua) /= => /esym /[swap] /[apply].
rewrite [in X in _ -> _ = X]orbC.
apply=> //.
  by rewrite eq_sym.
by move: uvab; rewrite [X in _ =i X -> _]fsetUC.
Qed.

Lemma biboundary_fsetMDdiag (e : `E G) :
  biboundary e = `d e `*` `d e `\` fset_diag (`d e).
Proof.
rewrite /biboundary.
case: cardfs2_sig=> -[] a b /= [] ab ->.
apply/eqP/fset_eqP=> x.
rewrite (surjective_pairing x) !inE in_fset_diag !inE xpair_eqE.
rewrite !(orb_andl, orb_andr) !(andb_orl, andb_orr) /=.
move: (ab); apply: id2b_andr.
have[->|x1a]:= eqVneq x.1 a=> /=.
all: rewrite !((negPf ab), andbT, andbF, orbF) /=.
all: have[->|x2a]:= eqVneq x.2 a=> /=.
all: rewrite !((negPf ab), andbT, andbF, orbF, andbb) //=.
  by rewrite (negPf x1a) andbF.
have[->|x1b]:= eqVneq x.1 b=> //=.
by rewrite eq_sym andNb.
Qed.

Lemma in_biboundary (e : `E G) a b :
  ((a, b) \in biboundary e) = (`d e == [fset a; b]).
Proof.
pose f (p : `V G * `V G) := let: (x,y) := p in [fset x; y].
apply/idP/idP.
  rewrite /biboundary.
  case: cardfs2_sig => -[u v] /= [] uv ->.
  by rewrite !inE => /orP [] /eqP abuv; rewrite -/(f (a, b)) abuv // fsetUC.
move /eqP /biboundaryE ->.
by rewrite !inE eqxx.
Qed.

Lemma in_biboundary_neq (e : `E G) (a b : `V G) :
  (a, b) \in biboundary e -> a != b.
Proof.
rewrite in_biboundary=> deab.
apply/eqP; move: deab=> /[swap] ->.
move/eqP/(congr1 (size \o val)).
by rewrite /= fsetUid boundary_card2 cardfs1.
Qed.

Lemma cardfs_biboundary (e : `E G) : #|` biboundary e | = 2.
Proof.
rewrite /biboundary.
case: cardfs2_sig => [] [u v] [uv deuv].
rewrite cardfs2 /=.
suff-> : (u, v) != (v, u) by [].
by rewrite xpair_eqE (eq_sym v u) !(negPf uv).
Qed.

Lemma boundary_biboundary_eq (e f : `E G) :
 (`d e == `d f) = (biboundary e == biboundary f).
Proof.
have := cardfs2_sig (boundary_card2 e) => -[] [] a b /= [] ab deab.
have := cardfs2_sig (boundary_card2 f) => -[] [] c d /= [] cd dfcd.
apply/idP/idP.
  move/eqP.
  rewrite dfcd => /biboundaryE ->.
  by rewrite (biboundaryE dfcd).
move/eqP/fsetP/(_ (a,b)).
rewrite (biboundaryE deab) in_biboundary 2!inE eqxx /=.
move/esym/eqP ->.
by apply/eqP.
Qed.

(* TODO: restate in terms of trivIset *)
Lemma ex_biboundary_eq (e f : `E G) :
  (exists p, (p \in biboundary e) && (p \in biboundary f)) ->
  biboundary e = biboundary f.
Proof.
case=> -[a b] /andP [].
by rewrite !in_biboundary => /eqP /biboundaryE -> /eqP /biboundaryE ->.
Qed.

Lemma boundary_biboundary_inj :
  injective (fun e : `E G => `d e) <-> injective biboundary.
Proof.
by split; move=> H e f /eqP;
                 [ rewrite -boundary_biboundary_eq => /eqP
                 | rewrite boundary_biboundary_eq => /eqP ];
                 exact: H.
Qed.

End biboundary.

(* 0-coskeleton *)
Module CompleteGraph.
Section def.
Variable V : finType.
Definition E :=
  [fset [fset p.1; p.2] |
    p in ([fset: V] `*` [fset: V]) `\` fset_diag [fset: V]].
Definition boundary (e : E) : {fset V} := val e.
Definition axiom : forall e : E, #|` boundary e| = 2.
Proof.
move=> e; rewrite /boundary.
case: e => e /= /imfsetP [] [a b] /= /imfsetP [] [a' b'] /=.
rewrite !inE /= in_fset_diag !inE /= => p [] -> -> ->.
by rewrite cardfs2 p.
Qed.
Definition t := LooplessUndirectedGraph.mk axiom.
End def.
End CompleteGraph.

Notation "`K" := CompleteGraph.t (at level 0, format "`K").
Notation "`K_ n" := (CompleteGraph.t 'I_n)
                     (at level 1, format "`K_ n").

(* TODO?: define Module CompleteGraph using is_complete_graph *)
Section is_complete_graph.
Implicit Type G : llugraph.

(*
Definition is_KT G := isomorphic G (`K `V G).
*)

Definition is_overcomplete_graph G :=
  forall v w : `V G, v != w -> exists e : `E G, `d e = [fset v; w].

Definition is_complete_graph G :=
  injective (fun e : `E G => `d e) /\ is_overcomplete_graph G.

Lemma complete_graph_is_overcomplete G :
  is_complete_graph G -> is_overcomplete_graph G.
Proof. by case. Qed.

Lemma KT_is_complete (T : finType) : is_complete_graph (`K T).
Proof.
split; first by move=> *; apply: val_inj.
move=> v w vw.
have eP : [fset v; w] \in CompleteGraph.E T.
  apply/imfsetP; exists (v, w) => //=.
  by rewrite !inE in_fset_diag in_fsetT /= vw.
by exists [` eP] => /=.
Qed.

Lemma card_VKn n : #| `V `K_n | = n.
Proof. exact: card_ord. Qed.

Lemma card_Ecomplete_aux G :
  is_overcomplete_graph G ->
  fcover [fset biboundary e | e in `E G]  =
    ([fset: `V G] `*` [fset: `V G]) `\` fset_diag [fset: `V G].
Proof.
move=> d_surj.
rewrite /fcover -imfsetT bigfcup_image.
under eq_bigr do rewrite biboundary_fsetMDdiag.
apply/fsetP=> -[a b]; apply/idP/idP.
  move/bigfcupP=> [] S /andP ?.
  rewrite !(inE, in_fset_diag) /=.
  case: (a == b)=> //.
  by rewrite andbT /= andbA andNb.
rewrite !(inE, in_fset_diag) /= andbT => /[dup] ab /d_surj [] e deab.
apply/bigfcupP; exists e; first by rewrite inE.
rewrite !(inE, in_fset_diag) /= (negPf ab) andbF /=.
by rewrite deab !inE !eqxx orbT.
Qed.

Lemma card_Ecomplete G :
  is_complete_graph G -> (2 * #| `E G | = #| `V G | * (#| `V G | - 1)).
Proof.
case=> /boundary_biboundary_inj d_inj.
move=> /card_Ecomplete_aux /(congr1 (size \o val)) /=.
rewrite cardfs_diagC cardfsT => <-.
rewrite (eqTleqif (leq_card_fcover _)); last first.
  apply/trivIfsetP=> /= d1 d2 /imfsetP [] e1 ? -> /imfsetP [] e2 ? ->.
  apply: contraR=> /fset0Pn [] /= p /[!inE] /andP [] p1 p2.
  apply/eqP/ex_biboundary_eq.
  by exists p; rewrite p1 p2.
rewrite [RHS](_ : _ = \sum_(A <- [fset biboundary e | e in `E G]) 2).
  rewrite big_const_seq iter_addn addn0 count_predT.
  by rewrite card_imfset//= cardE.
rewrite !big_seq.
apply: eq_bigr => b /imfsetP [] e _ ->.
by rewrite cardfs_biboundary.
Qed.

Lemma card_EG_leq_Ecomplete G :
  injective (fun e : `E G => `d e) ->
  (2 * #| `E G | <= #| `V G | * (#| `V G | - 1)).
Proof.
move=> ib.
apply: (@leq_trans (2 * #| `E (`K (`V G)) |)); last first.
  rewrite (_ : #| `V G | = #| `V (`K (`V G)) |) //.
  rewrite card_Ecomplete //.
  exact: KT_is_complete.
rewrite leq_mul2l //=.
have-> : #| `E G | = #|` [fset `d e | e in [fset: `E G]] |.
  by rewrite card_imfset //= cardfsT.
rewrite -cardfE.
apply/fsubset_leq_card/fsubsetP=> x.
move/imfsetP=> [] e /= _ ->.
apply/imfsetP => /=.
have:= boundary_sig2 e => -[] [] a b /= [] ab ->.
exists (a, b) => //.
by rewrite !inE in_fset_diag in_fsetT (negPf ab).
Qed.

Lemma nindmatch_complete G :
  is_overcomplete_graph G ->
  nindmatch G <= 1 ?= iff (2 <= #| `V G |).
Proof.
move=> cmp.
have-> : (2 <= #| `V G |) = (1 <= #| `E G |).
  apply/idP/idP.
    move/card_gt1P=> [] x [] y [] xVG yVG xy.
    have:= cmp x y xy => -[] e dexy.
    by apply/card_gt0P; exists e.
  move/card_gt0P=> [] e eEG.
  have:= boundary_sig2 e => -[] [] x y /= [] xy dexy.
  by apply/card_gt1P; exists x, y; split.
apply/leqifP; case: ifPn=> [EGgt0 |]; last first.
  by rewrite -leqNgt leqn0 => /eqP /nindmatch0 ->.
have: 1 <= nindmatch G by rewrite ltnNge leqn0 nindmatch_eq0 -lt0n.
rewrite leq_eqVlt=> /orP [/eqP -> // |].
have:= exists_nindmatch G => -[] M Mim ->.
have:= Mim => /induced_matchingP Mim'.
rewrite cardfE=> /card_gt1P /= [] e1 [] e2 [] ? ? e12.
exfalso.
have: `d (\val e2) `\` `d (\val e1) != fset0.
  rewrite fsetD_eq0; apply/negP=> /fsubset_leqif_cards.
  rewrite !boundary_card2.
  apply/leqif_refl/eqP=> /esym de12.
  have:= matching_inj_boundary (induced_sub_matching Mim).
  move/(_ (\val e1) (\val e2) (fsvalP _) (fsvalP _) de12)/val_inj.
  by apply/eqP.
pose v1 := get1_boundary (\val e1).
case/fset0Pn=> v2 /[!in_fsetD] /andP [] ve1 ve2.
have:= cmp v1 v2 => -[].
  by apply/eqP; move: ve1=> /[swap] <- /[!get1_in_boundary].
move=> e3 de3.
have e12': \val e1 != \val e2.
  by apply/eqP=> /val_inj; move: e12 => /[swap] ->; rewrite eqxx.
have:= Mim' (\val e1) (\val e2) (fsvalP _) (fsvalP _) e12 e3.
by case=> /fset0Pn; apply; [exists v1 | exists v2];
   rewrite de3 !inE eqxx ?orbT andbT// get1_in_boundary.
Qed.

Lemma maximal_matching_complete G (S : {fset `E G}) :
  is_overcomplete_graph G -> S \in maximal_matching G ->  #|` S | = #| `V G | ./2.
Proof.
move=> cmp SmG.
apply/eqP; move: SmG; apply: contraLR.
rewrite neq_ltn => /orP [] H; apply/maximal_matchingP => -[]; last first.
  move => SmG _.
  have := double_nmatch_leq_cardVG G.
  rewrite -geq_half_double.
  have := leq_nmatch SmG.
  move/leq_trans/[apply].
  by rewrite leqNgt H.
move=> SmG Smax; move: H.
rewrite geq_half_double -addn1 doubleD.
rewrite -matching_double_card //.
rewrite -leq_psubRL //.
rewrite -cardfsT -cardfsDS; last by apply/fsubsetP => ?; rewrite inE.
case/cardfs_gt1_sig => -[] a b /= [] ab [].
rewrite !inE 2!andbT => aS bS.
have := cmp a b ab => -[] e deab.
have eS : e \notin S.
  apply/negP=> H.
  move/negP: aS; apply.
  apply/bigfcupP; exists (`d e); last by rewrite deab !inE eqxx.
  by rewrite in_imfset.
have := Smax (e |` S).
move/(_ _)/negP; apply; first exact: fproperU1.
apply/matchingP => x y; rewrite !inE.
case/orP => [/eqP -> | xS]; case/orP => [/eqP -> | yS]; rewrite ?eqxx //= => xy.
- apply/fdisjointP=> u.
  by rewrite deab !inE=> /orP [] /eqP ->; apply/negP => ad;
     [move/bigfcupP: aS | move/bigfcupP: bS];
     apply; exists (`d y) => //; rewrite in_imfset.
- rewrite fdisjoint_sym.
  apply/fdisjointP=> u.
  by rewrite deab !inE=> /orP [] /eqP ->; apply/negP => ad;
     [move/bigfcupP: aS | move/bigfcupP: bS];
     apply; exists (`d x) => //; rewrite in_imfset.
- by move/matchingP: SmG; apply.
Qed.

Lemma nmatch_complete G : is_overcomplete_graph G -> nmatch G = #| `V G | ./2.
Proof.
move/maximal_matching_complete=> H.
rewrite -nmaxmatchE.
by have:= exists_nmaxmatch G => -[] M /H -> ->.
Qed.

Lemma nminmatch_complete G : is_overcomplete_graph G -> nminmatch G = nmatch G.
Proof.
move=> icg.
move/maximal_matching_complete: (icg) => H.
rewrite nmatch_complete //.
by have:= exists_nminmatch G => -[] M /H -> ->.
Qed.

End is_complete_graph.

Module CompleteBipartiteGraph.
Section def.
Variables V1 V2 : finType.
Definition V := (V1 + V2)%type.
Definition E := (V1 * V2)%type.
Definition boundary (e : E) : {fset V} := [fset inl e.1; inr e.2].
Lemma axiom (e : E) : #|` boundary e| = 2.
Proof. by case: e => x y; rewrite /boundary /= cardfs2. Qed.
Definition t := LooplessUndirectedGraph.mk axiom.
End def.
Section lemmas.
Lemma boundary_inj V1 V2 : injective (@boundary V1 V2).
Proof.
rewrite /boundary; case=> a1 b1 [] a2 b2 /fsetP /= H.
have:= H (inl a2).
rewrite !inE eqxx /= -/(is_true _) => /orP [/eqP [] -> |]; last discriminate.
have:= H (inr b2).
rewrite !inE eqxx orbT -/(is_true _) => /orP [| /eqP [] -> //].
discriminate.
Qed.
End lemmas.
End CompleteBipartiteGraph.

Notation "`K2"
  := (CompleteBipartiteGraph.t)
       (at level 0, format "`K2").
Notation "`K2_ m n"
  := (CompleteBipartiteGraph.t `I_m `I_n)
       (at level 1, format "`K2_ m n").

Section is_complete_bipartite.
Implicit Type G : llugraph.

Definition is_complete_bipartite_graph G :=
  injective (fun e : `E G => `d e) /\
    exists V_1 V_2 : {fset `V G},
      [fset: `V G] = V_1 `|` V_2 /\ V_1 `&` V_2 = fset0 /\
        forall v : V_1, forall w : V_2,
        exists e : `E G, `d e = [fset \val v; \val w].

Lemma KV1V2_is_complete_bipartite (V1 V2 : finType) :
  is_complete_bipartite_graph (`K2 V1 V2 ).
Proof.
rewrite /is_complete_bipartite_graph /=.
split; first exact: CompleteBipartiteGraph.boundary_inj.
exists (inl @` V1), (inr @` V2).
split.
  apply/esym/eqP; rewrite eqEfsubset => /=.
  rewrite fsubsetT/= fsubsetE.
  by case=> v _; rewrite inE in_imfset// orbT.
split.
  apply/fsetP=> v.
  rewrite inE; case: imfsetP=> //= -[] x ? ->.
  case: imfsetP=> //= -[] y ?.
  discriminate.
move=> v w.
have: \val v \in inl @` V1 by exact: valP.
case/imfsetP=> x ? ->.
have: \val w \in inr @` V2 by exact: valP.
case/imfsetP=> y ? ->.
by exists (x, y).
Qed.

Lemma card_VK2 (V1 V2 : finType) :
  #| `V (`K2 V1 V2)| = (#| V1| + #| V2|)%N.
Proof. exact: card_sum. Qed.

Lemma card_EK2 (V1 V2 : finType) :
  #| `E (`K2 V1 V2)| = (#| V1| *  #| V2|)%N.
Proof. exact: card_prod. Qed.

(*
(* TODO: move to graph.v *)
Lemma nindmatch_eq1P G :
  reflect
    (forall S : {fset `E G}, S \in induced_matching G -> #|` S | = 1)
    (nindmatch G == 1).
Proof.
rewrite /nindmatch /=.
set maxS := eqbLHS.
pose argmaxS : {fset `E G} :=
  [arg max_(S > fset0 in induced_matching G) #|` S|].
have maxSE: maxS = #|` argmaxS|.
  by rewrite /maxS (bigop.bigmax_eq_arg fset0)// fset0_induced_matching.
apply: (iffP idP).
  move=> /eqP max1 (* /[dup] /eq_leq leq1 max1.*) .
  have:= leq_bigmax
*)

Lemma nindmatch_complete_bipartite G (e : `E G) :
  is_complete_bipartite_graph G -> nindmatch G = 1.
Proof.
move=> icbg.
rewrite /nindmatch /=.
rewrite /induced_matching /=.
Abort.

Lemma nminmatch_complete_bipartite (V1 V2 : finType) :
  nminmatch (`K2 V1 V2) = minn #| V1| #| V2|.
Proof.
Abort.

Lemma nmatch_complete_bipartite (V1 V2 : finType) :
  nmatch (`K2 V1 V2) = minn #| V1| #| V2|.
Proof.
Abort.

End is_complete_bipartite.
