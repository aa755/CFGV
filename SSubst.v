(*

  Copyright 2014 Cornell University

  This file is part of CFGV project.

  CFGV is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  CFGV is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CFGV.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/CFGVLFMTP2014/
  Authors: Abhishek Anand & Vincent Rahli

*)
Set Implicit Arguments.
Require Export SubstAuxAlphaEq.
Require Export AlphaRen.
Require Export Term.
(** printing #  $\times$ #Ã—# *)
(** printing &  $\times$ #Ã—# *)
(** printing ==  $=_{\alpha}$ #=a=# *)
(** printing ===  $=_{\alpha}$ #=a=# *)
(** printing =$=  $\approx$ #=set=# *)
(* printing --  $\minus \minus$ #--# *)


(** CatchFileBetweenTagsSSubstStart *)

Definition tSSubst {G} {vc: VarSym G } {gs} 
    (t : Term gs) (sub : SSubstitution vc) : Term gs :=
  let tr := tRenAlpha t (rangeFreeVars sub)
  in tSSubstAux tr sub.

(** CatchFileBetweenTagsSSubstEnd *)

Notation Dom := ALDom.
Notation fvr := rangeFreeVars.
Notation "sa =$= sb" := (eqset sa sb)
   (at level 109, right associativity).


Section GramVC.
Variable G : CFGV. 
Variable vc  : VarSym G.
Notation fv := (tfreevars vc).
Notation "x == y" := (tAlphaEq vc x y)
   (at level 69, right associativity).
Notation "sa === sb" := (AlphaEqSubst sa sb)
   (at level 69, right associativity).

Definition SubstSub (sa sb : SSubstitution vc):=
ALMapRange (fun t => tSSubst t sb) sa.

Definition change_bvars_range 
  (lva : list (vType vc)) 
  (sub: SSubstitution vc) : SSubstitution vc:=
  map (fun p  => (fst p, tRenAlpha (snd p) lva )) sub.

Lemma change_bvars_range_spec : forall lva sub,
  let sub' := (change_bvars_range lva sub) in 
  sub === sub' #
  disjoint (flat_map (tBndngVarsDeep vc) (ALRange sub')) lva.
Proof.
  induction sub as [ |(v,t) sub Hind];
  allsimpl; cpx. repnd.
  pose proof (tcase (@RenAlphaAvoid G vc)).
  pose proof (tcase (@RenAlphaAlpha G vc)).
  dands; cpx; repeat (disjoint_reasoning).
  unfold AlphaEqSubst. simpl.
  dands; cpx.
Qed.

Lemma change_bvars_rangewspec: forall
  (lva : list (vType vc)) 
  (sub: SSubstitution vc),
  {sr : SSubstitution vc $
   sub === sr #
  disjoint (flat_map (tBndngVarsDeep vc) (ALRange sr)) lva}.
Proof.
  intros.
  eexists; apply change_bvars_range_spec.
Qed.
  
Section SSubstRespectsAlpha.

Context {gs : GSym G}
  (a b : Term gs) (sa :  SSubstitution vc).


Lemma SSubstRespectsAlpha1 :
a == b -> (tSSubst a sa) == (tSSubst b sa).
Proof.
  introv Ha.
  unfold tSSubst.
  pose proof ((tcase (@RenAlphaAlpha G vc))
                gs a (rangeFreeVars sa)) as Hala.
  pose proof ((tcase (@RenAlphaAlpha G vc))
                gs b (rangeFreeVars sa)) as Halb.
  pose proof (tcase (@RenAlphaAvoid G vc)) as Hav.
  apply (ALtcase (@SubstAuxRespectsAlpha G vc));
  eauto with Alpha.
  repeat (disjoint_reasoning).
Qed.

Context (sb :  SSubstitution vc).
Lemma SSubstRespectsAlpha :
(** CatchFileBetweenTagsSubRespAlphaStart *)

a == b -> sa === sb -> tSSubst a sa == tSSubst b sb.

(** CatchFileBetweenTagsSubRespAlphaEnd *)

Proof.
  introv Ha Has.
  unfold tSSubst.
  pose proof (ALtcase (@SubstAuxRespectsAlpha G vc)) as Hra.
  pose proof ((tcase (@RenAlphaAlpha G vc))
                gs a (rangeFreeVars sa)) as Hala.
  pose proof ((tcase (@RenAlphaAlpha G vc))
                gs b (rangeFreeVars sb)) as Halb.
  assert ((tRenAlpha a (rangeFreeVars sa)) 
          == (tRenAlpha b (rangeFreeVars sb))) as Hx by
  eauto 4 with Alpha.
  pose proof (tcase (@RenAlphaAvoid G vc)) as Hav.
  apply SubstAuxRespectsAlpha2; cpx.
Qed.
End SSubstRespectsAlpha.

Notation filter := SubFilter.
Notation keepFirst := SubKeepFirst.

Section S1Term1Sub1Lv.

Lemma SSubstFVarsDisjoint:
forall (s : GSym G) (t : Term s) (sub : SSubstitution vc) lf,
    disjoint (tfreevars vc t) lf 
    -> disjoint (rangeFreeVars sub) lf 
    -> disjoint (tfreevars vc (tSSubst t sub)) lf.
Proof.
  introv H1d H2d.
  pose proof (tRenWithSpec t (fvr sub)) as Hfr.
  exrepnd.
  duplicate Hfr1 as Hb.
  apply (ALtcase  alpha_preserves_free_vars) in Hb.
  rewrite Hb in H1d. clear Hb.
  apply SSubstRespectsAlpha1
    with (sa:=sub)  in Hfr1.
  apply (ALtcase alpha_preserves_free_vars) in Hfr1.
  rewrite Hfr1.
  rename tar into ar.
  clear dependent t.
  unfold tSSubst.
  rewrite <- (tcase RenAlphaNoChange) by cpx.
  introv Hin.
  apply (tcase (@free_vars_SSubstAux G vc)) in Hin; cpx;[].
  rw in_app_iff in Hin.
  dorn Hin; cpx.
  + apply in_diff in Hin. repnd.
    introv Hinc; disjoint_lin_contra.
  + rw disjoint_flat_map_l in H2d.
    allsimpl.
    rw lin_flat_map in Hin.
    exrepnd.
    rw in_map_iff in Hin1.
    exrepnd. allsimpl. subst.
    rw ALKeepFirstLin in Hin1.
    repnd.
    apply ALFindSome in Hin2.
    apply ALInEta in Hin2.
    repnd.
    apply H2d in Hin2.
    apply Hin2.
    cpx.
Qed.


Lemma SubstSubFVarsDisjoint:
forall (sa sb : SSubstitution vc) lf,
    disjoint (fvr sa ++ fvr sb) lf 
    -> disjoint (fvr (SubstSub sa sb)) lf.
Proof.
  induction sa as [| (v,t)  sa Hind]; introv Hd; allsimpl;
    [unfold rangeFreeVars; cpx |].
  rewrite rangeFreeVars_cons.
  rewrite rangeFreeVars_cons in Hd.
  repeat (disjoint_reasoning); cpx;
  [|apply Hind; repeat (disjoint_reasoning)].
  apply SSubstFVarsDisjoint; auto.
Qed.

Lemma SubstSubAsSubstAux:
forall (sa sb : SSubstitution vc),
    disjoint (flat_map (tBndngVarsDeep vc) (ALRange sa)) 
             (fvr sb)
    -> SubstSub sa sb = tSSubstAux_sub sa sb.
Proof.
  induction sa as [| (v,t)  sa Hind]; introv Hd; allsimpl;
    [unfold rangeFreeVars; cpx |].
  repeat (disjoint_reasoning).
  f_equal; cpx;[].
  f_equal; cpx.
  unfold tSSubst.
  rewrite <- (tcase RenAlphaNoChange) by cpx.
  refl.
Qed.

Lemma SSubstRespectsAlpha2 :
forall {gs : GSym G}
  (a b : Term gs) (sa sb:  SSubstitution vc),
  a == b -> (tSSubst (tSSubst a sa) sb) 
            == (tSSubst (tSSubst b sa) sb).
Proof.
  introv Ha.
  apply SSubstRespectsAlpha1.
  apply SSubstRespectsAlpha1.
  trivial.
Qed.


Lemma SSubstSubRespectsAlpha : forall sa1 sb sa2,
  sa1 === sa2 
  -> SubstSub sa1 sb === SubstSub sa2 sb.
Proof.
  intros ?.
  unfold AlphaEqSubst.
  induction sa1 as [|(v1,t1) subl1 Hind]; intros ? ? Hals;
  destruct 
    sa2 as [|(v2,t2) subl2]; allsimpl;sp.
  unfold AlphaEqSubst.
  apply SSubstRespectsAlpha1; assumption.
Qed.

Context {gs : GSym G}
  (a: Term gs) (s :  SSubstitution vc)
  (l: list (vType vc)).


Lemma SSubstFilter :
(** CatchFileBetweenTagsSubFiltStart *)

disjoint l (fv a) -> tSSubst a s == tSSubst a (filter s l).

(** CatchFileBetweenTagsSubFiltEnd *)

Proof.
  introv Hdis.
  unfold tSSubst.
  pose proof ((tcase (@RenAlphaAlpha G vc))
                gs a (rangeFreeVars s)) as Hala.
  
  pose proof ((tcase (@RenAlphaAlpha G vc))
                gs a ((rangeFreeVars (SubFilter s l)))) 
      as Halb.
 assert 
  ((tRenAlpha a (rangeFreeVars (SubFilter s l)))
    == (tRenAlpha a (rangeFreeVars s))) as Halc
    by eauto with Alpha.
  pose proof (tcase (@RenAlphaAvoid G vc)) as Hav.
  pose proof (Hav _ a (rangeFreeVars s)) as Havs.
  apply (ALtcase (@SubstAuxRespectsAlpha G vc))
    with (sub:=(SubFilter s l))  in Halc;
  eauto;[
   | repeat (disjoint_reasoning);
    unfold SubFilter; SetReasoning; fail].
  apply (tcase alphaEqSym) in Halc.
  eapply (tcase alphaEqTransitive);
  [ | apply Halc].
  apply talphaEqRefl.
  apply  (tcase (SSubstAuxSubFilter G vc)).
  apply alpha_preserves_free_vars in Hala.
  rw <- Hala.
  disjoint_reasoning.
Qed.

End S1Term1Sub1Lv.

Section S1Term1Sub.

Context {gs : GSym G}
  (a: Term gs) (s :  SSubstitution vc).


Theorem FVSSubst:
(** CatchFileBetweenTagsEqSetStart *)

fv (tSSubst a s) =$= (fv a -- Dom s) ++ fvr (keepFirst s (fv a)).

(** CatchFileBetweenTagsEqSetEnd *)

Proof.
  unfold tSSubst.
  addRenSpec.
  apply alpha_preserves_free_vars in Hala.
  rw  Hala.
  apply free_vars_SSubstAux.
  trivial.
Qed.

End S1Term1Sub.

Section S1Term2Sub.

Context {gs : GSym G}
  (a: Term gs) (sa sb :  SSubstitution vc).

Theorem SSubstNestSwap:

(** CatchFileBetweenTagsSwapNestStart *)

disjoint (fvr sa) (Dom sb)
-> disjoint (fvr sb) (Dom sa)
-> disjoint (Dom sa) (Dom sb)
-> tSSubst (tSSubst a sa) sb == tSSubst (tSSubst a sb) sa.

(** CatchFileBetweenTagsSwapNestEnd *)

Proof.
  introns Hdis.
  pose proof (change_bvars_rangewspec
       (rangeFreeVars sa) sb) as Hfs.
  exrepnd.
  rename sr into sb'.
  duplicate Hfs1 as Hdom.
  duplicate Hfs1 as Hfv.
  duplicate Hfs1 as Hb.
  unfold AlphaEqSubst in Hdom.
  apply ALRangeRelSameDom in Hdom.
  apply subAlphaSameFV in Hfv.
  apply SSubstRespectsAlpha with (a0:=a) (b:=a) in Hfs1;
    [|eauto with Alpha].
  apply SSubstRespectsAlpha1 with (sa0:=sa) in Hfs1.
  eapply (tcase alphaEqTransitive);
  [ |apply (ALtcase alphaEqSym) ; apply Hfs1].
  rewrite Hdom in Hdis.
  rewrite Hdom in Hdis1.
  rewrite Hfv in Hdis0.
  clear Hdom  Hfv Hfs1.
  apply SSubstRespectsAlpha with (a0:=(tSSubst a sa)) 
            (b:=(tSSubst a sa)) in Hb;
    [|eauto with Alpha].
  eapply (tcase alphaEqTransitive);
    [apply Hb|].
  clear dependent sb.
  rename sb' into sb.
  rename Hfs0 into Hdisrb.
  pose proof (change_bvars_rangewspec
       (rangeFreeVars sb) sa) as Hfs.
  exrepnd.
  rename sr into sa'.
  duplicate Hfs1 as Hdom.
  duplicate Hfs1 as Hfv.
  duplicate Hfs1 as Hb.
  unfold AlphaEqSubst in Hdom.
  apply ALRangeRelSameDom in Hdom.
  apply subAlphaSameFV in Hfv.
  apply SSubstRespectsAlpha with (a0:=a) (b:=a) in Hfs1;
    [|eauto with Alpha].
  apply SSubstRespectsAlpha1 with (sa0:=sb) in Hfs1.
  eapply (tcase alphaEqTransitive);
    [ apply Hfs1 | ].
  rewrite Hdom in Hdis1.
  rewrite Hdom in Hdis0.
  rewrite Hfv in Hdis.
  rewrite Hfv in Hdisrb.
  clear Hdom  Hfv Hfs1.
  apply SSubstRespectsAlpha with (a0:=(tSSubst a sb)) 
            (b:=(tSSubst a sb)) in Hb;
    [|eauto with Alpha].
  apply (tcase alphaEqSym) in Hb.
  eapply (tcase alphaEqTransitive);[ | apply Hb].
  clear dependent sa.
  rename sa' into sa.
  pose proof 
    (tRenWithSpec a (fvr sa ++ fvr sb)) as Hfr.
  exrepnd.
  rename tar into ar.
  duplicate Hfr1.
  apply SSubstRespectsAlpha2 
    with (sa0:=sa) (sb0:=sb) in Hfr1.
  apply SSubstRespectsAlpha2 
    with (sa0:=sb) (sb0:=sa) in Hfr2.
  assert ((tSSubst (tSSubst ar sa) sb) 
          == (tSSubst (tSSubst ar sb) sa));
       [ | eauto with Alpha; fail].
  clear dependent a.
  unfold tSSubst.
  repeat (disjoint_reasoning).
  pattern (tRenAlpha ar (fvr sa)).
  rewrite <- (tcase RenAlphaNoChange); sp;[].
  pattern (tRenAlpha ar (fvr sb)).
  rewrite <- (tcase RenAlphaNoChange); sp;[].
  rewrite <- (tcase RenAlphaNoChange);
  [| apply (tcase (@SSubstAuxBVarsDisjoint G vc)); cpx].
  rewrite <- (tcase RenAlphaNoChange);
  [| apply (tcase (@SSubstAuxBVarsDisjoint G vc)); cpx].
  apply talphaEqRefl.
  apply (tcase (@SSubstAuxNestSwap G vc));
    repeat (disjoint_reasoning).
Qed.


Theorem SSubstNestAsApp:

(** CatchFileBetweenTagsNestAppStart *)

tSSubst (tSSubst a sa) sb == tSSubst a ((SubstSub sa sb)++sb).

(** CatchFileBetweenTagsNestAppEnd *)

Proof.
  pose proof (change_bvars_rangewspec
       (rangeFreeVars sb) sa) as Hfs.
  exrepnd.
  rename sr into sa'.
  duplicate Hfs1 as Hb.
  apply SSubstRespectsAlpha with (a0:=a) (b:=a) in Hfs1;
    [|eauto with Alpha].
  apply SSubstRespectsAlpha1 with (sa0:=sb) in Hfs1.
  eapply (tcase alphaEqTransitive);
    [apply Hfs1|].
  assert (AlphaEqSubst (SubstSub sa sb ++ sb)
                       (SubstSub sa' sb ++ sb)) as Hals by 
      (apply AlphaEqSubstApp;[apply SSubstSubRespectsAlpha; assumption
                              | eauto with Alpha]).
  apply SSubstRespectsAlpha with (a0:=a) (b:=a) in Hals;
    [|eauto with Alpha].
  apply (tcase alphaEqSym) in Hals.
  eapply (tcase alphaEqTransitive);
    [| apply Hals].
  clear dependent sa.
  rename sa' into sa.
  pose proof 
    (tRenWithSpec a (fvr sa ++ fvr sb)) as Hfr.
  exrepnd.
  rename tar into ar.
  duplicate Hfr1.
  apply SSubstRespectsAlpha2 
    with (sa0:=sa) (sb0:=sb) in Hfr1.
  eapply (tcase alphaEqTransitive);
    [apply Hfr1 | ]. clear Hfr1.
  apply SSubstRespectsAlpha1 
    with (sa0:=(SubstSub sa sb ++ sb))  in Hfr2.
  apply (tcase alphaEqSym) in Hfr2.
  eapply (tcase alphaEqTransitive);
    [| apply Hfr2 ].
  clear dependent a.
  unfold tSSubst.
  repeat (disjoint_reasoning).
  pattern (tRenAlpha ar (fvr sa)).
  rewrite <- (tcase RenAlphaNoChange) by cpx.
  rewrite <- (tcase RenAlphaNoChange) by
    (apply (tcase (@SSubstAuxBVarsDisjoint G vc)); 
        cpx).
  rewrite <- (tcase RenAlphaNoChange);
  [ |rewrite rangeFreeVarsApp;
     disjoint_reasoning; cpx;[];
     apply disjoint_sym; apply SubstSubFVarsDisjoint;
     repeat(disjoint_reasoning); fail].
  rewrite  SubstSubAsSubstAux; cpx;[].
  apply talphaEqRefl.
  apply (tcase (@SSubstAuxNestAsApp G vc)).
  cpx.
Qed.

End S1Term2Sub.

End GramVC.
