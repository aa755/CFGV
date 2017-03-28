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

Require Export AlphaEquality.
Require Export SwapProps.

Set Implicit Arguments.

(** (re)defining it this way enables coq to successfully
    match the statement of [alphaEqTransitive]
    with the lemma [GAlphaInd] *)
Definition transRel {T : [univ]} (R : bin_rel T) :=  
forall x y : T, 
  R x y 
  -> forall z : T,
     R y z -> R x z.

Lemma MakeAbsPnodeSame : forall 
  {G : CFGV} {vc : VarSym G}
  (lps : list (GSym G))
  (m: Mixture (map (fun x : GSym G => (true, x)) (lps))),
  (MakeAbstractionsPNode vc m)
    = (MakeAbstractionsTNodeAux vc [] m).
Proof.
  induction m; cpx.
Qed.

Ltac remAlphaRight Hyp name :=  
  match type of Hyp with
  | pAlphaEq _ _ ?r => remember r as name
  | tAlphaEq _ _ ?r => remember r as name
  end.

Ltac remAlphaLeft Hyp name :=  
  match type of Hyp with
  | pAlphaEq _ ?l _ => remember l as name
  | tAlphaEq _ ?l _ => remember l as name
  end.


Section AlphaProps.
Context {G : CFGV} {vc  : VarSym G}.

Lemma alphaEquiVariant :
( 
  (forall (s : GSym G) ,
      EquiVariantRelSame (@tSwap G vc s) (tAlphaEq vc)) 
   *
  (forall (s : GSym G),
      EquiVariantRelSame (@pSwap G vc s) (pAlphaEq vc))
  *
  (EquiVariantRelSame (@swapAbs G vc) (@AlphaEqAbs G vc))
  *
  (EquiVariantRelSame (@swapLAbs G vc) (@lAlphaEqAbs G vc))
).
Proof.
  intros. GAlphaInd; introns Hyp; intros; 
  allsimpl; try (econstructor; eauto; fail);[| | |].
- Case "tnode". constructor.
  unfold allBndngVars.
  rw <- swapLBoundVarsCommute.
  rw <- swapLBoundVarsCommute.
  rewrite <- MakeLAbsSwapCommute.
  rewrite <- MakeLAbsSwapCommute.
  cpx.
- Case "pnode". constructor.
  rewrite <- MakeAbsPNodeCommute.
  rewrite <- MakeAbsPNodeCommute.
  cpx.
- Case "termAbs".
  specialize (Hyp4 sw).
  rewrite (tcase swap_app) in Hyp4.
  rewrite (tcase swap_app) in Hyp4.
  rewrite (tcase swap_prop_e1Stronger) in Hyp4.
  match type of Hyp4 with
  tAlphaEq _ _ ?b => pattern b in Hyp4
  end.
  rewrite (tcase swap_prop_e1Stronger) in Hyp4.
  rewrite <- (tcase swap_app) in Hyp4.
  rewrite <- (tcase swap_app) in Hyp4.

  unfold swapSwap in Hyp4. rewrite map_combine in Hyp4.
  rewrite map_combine in Hyp4.
  fold (swapLVar sw lbva) in Hyp4.
  fold (swapLVar sw lbvb) in Hyp4.
  fold (swapLVar sw lbnew) in Hyp4.
  remember (swapLVar sw lbnew) as lbns.
  repnud Hyp1.
  allsimpl.
  eapply  alAbT with (lbnew := lbns); eauto;
  try ( subst; unfold swapLVar; 
    autorewrite with fast; congruence; fail); cpx;
  subst;[unfolds_base; allsimpl;
  dands|];repeat (disjoint_reasoning);[ | | | | ].
  + rewrite <- (tcase AllVarsEquivariant).
    apply DisjointEquivariant; trivial.
  + rewrite <- (tcase AllVarsEquivariant).
    apply DisjointEquivariant; trivial.
  + apply NoRepeatsEquivariant; trivial.
  + apply DisjointEquivariant; trivial.
  + apply DisjointEquivariant; trivial.

- Case "patAbs".
  specialize (Hyp4 sw).
  rewrite (pcase swap_app) in Hyp4.
  rewrite (pcase swap_app) in Hyp4.
  rewrite (pcase swap_prop_e1Stronger) in Hyp4.
  match type of Hyp4 with
  pAlphaEq _ _ ?b => pattern b in Hyp4
  end.
  rewrite (pcase swap_prop_e1Stronger) in Hyp4.
  rewrite <- (pcase swap_app) in Hyp4.
  rewrite <- (pcase swap_app) in Hyp4.

  unfold swapSwap in Hyp4. rewrite map_combine in Hyp4.
  rewrite map_combine in Hyp4.
  fold (swapLVar sw lbva) in Hyp4.
  fold (swapLVar sw lbvb) in Hyp4.
  fold (swapLVar sw lbnew) in Hyp4.
  remember (swapLVar sw lbnew) as lbns.
  repnud Hyp1.
  allsimpl.
  eapply  alAbP with (lbnew := lbns); eauto;
  try ( subst; unfold swapLVar; 
    autorewrite with fast; congruence; fail); cpx;
  subst;[unfolds_base; allsimpl;
  dands|];repeat (disjoint_reasoning);[ | | | | ].
  + rewrite <- (pcase AllVarsEquivariant).
    apply DisjointEquivariant; trivial.
  + rewrite <- (pcase AllVarsEquivariant).
    apply DisjointEquivariant; trivial.
  + apply NoRepeatsEquivariant; trivial.
  + apply DisjointEquivariant; trivial.
  + apply DisjointEquivariant; trivial.
Qed.

Lemma tAlphaEqEquivariantRev : forall 
  (sw : Swapping vc) s (ta tb : Term s),
  tAlphaEq vc (tSwap ta sw) (tSwap tb sw)
  -> tAlphaEq vc ta tb.
Proof.
  introv Hd.
  apply (tcase alphaEquiVariant) in Hd.
  specialize (Hd (rev sw)).
  autorewrite with SwapAppR in Hd.
  autorewrite with fast in Hd.
  trivial.
Qed.

Lemma pAlphaEqEquivariantRev : forall 
  (sw : Swapping vc) s (ta tb : Pattern s),
  pAlphaEq vc (pSwap ta sw) (pSwap tb sw)
  -> pAlphaEq vc ta tb.
Proof.
  introv Hd.
  apply (tcase alphaEquiVariant) in Hd.
  specialize (Hd (rev sw)).
  autorewrite with SwapAppR in Hd.
  autorewrite with fast in Hd.
  trivial.
Qed.

(** todo : better name .. [lv] is not nil anymore *)
Lemma AlphaEqNilAbsT : forall 
(gs : GSym G) (tma tmb : Term gs)
(lv : list (vType vc)),
tAlphaEq vc tma tmb 
-> AlphaEqAbs (termAbs vc lv tma) (termAbs vc lv tmb).
Proof.
  introv Ha.
  pose proof (GFreshDistRenWSpec vc lv 
  (tAllVars tma++tAllVars tmb++lv))
    as XX.
  exrepnd. repeat (disjoint_reasoning).
  eapply  alAbT with (lbnew := lvn); eauto;
  unfold tFresh; dands;allsimpl;
  repeat(disjoint_reasoning); auto;[].
  apply alphaEquiVariant; cpx.
Qed.

Lemma AlphaEqNilAbsP : forall 
(gs : GSym G) (tma tmb : Pattern gs)
(lv : list (vType vc)),
pAlphaEq vc tma tmb 
-> AlphaEqAbs (patAbs vc lv tma) (patAbs vc lv tmb).
Proof.
  introv Ha.
  pose proof (GFreshDistRenWSpec vc lv 
  (pAllVars tma++pAllVars tmb++lv))
    as XX.
  exrepnd. repeat (disjoint_reasoning).
  eapply  alAbP with (lbnew := lvn); eauto;
  unfold pFresh; dands;allsimpl;
  repeat(disjoint_reasoning); auto;[].
  apply alphaEquiVariant; cpx.
Qed.
  
  
Notation vcType := (vType vc).
Notation vcAbstraction := (@Abstraction G vc).

Lemma alphaEqRefl : 
     (  (forall (s : GSym G) (t : Term s),
            tAlphaEq vc t t)
         *
        (forall (s : GSym G) (pt : Pattern s),
            pAlphaEq vc pt pt)
         *
        (forall (l : MixtureParam) (m : Mixture l) 
        (lbv : list (list (vType vc))),
           lAlphaEqAbs (MakeAbstractions vc m lbv) 
                       (MakeAbstractions vc m lbv))).
Proof.
  GInduction; introns Hyp; intros; cpx; allsimpl;
  try dlist_len lbv;  try (econstructor; eauto with slow; fail).
- Case "mtcons". econstructor; eauto;[].
  remember (lhead lbv) as lbvh.
  apply AlphaEqNilAbsT;cpx.
- Case "mpcons". econstructor; eauto;[].
  remember (lhead lbv) as lbvh.
  apply AlphaEqNilAbsP;cpx.
Qed.



Hint Resolve
(tcase alphaEqRefl)
(pcase alphaEqRefl)
(mcase alphaEqRefl)
  AlphaEqNilAbsT
  AlphaEqNilAbsP

 : Alpha.

Lemma talphaEqRefl : forall (s : GSym G) 
  (ta tb : Term s),
  ta=tb -> tAlphaEq vc ta tb.
Proof.
  intros. subst. eauto with Alpha.
Qed.


Require Import Eqdep_dec.



Hint Resolve deqMixP: Deq.

Lemma alphaEqSym :
(  (forall (s : GSym G) (ta tb : Term s),
      tAlphaEq vc ta tb -> tAlphaEq vc tb ta)
   *
  (forall (s : GSym G) (pta ptb : Pattern s),
      pAlphaEq vc pta ptb -> pAlphaEq vc ptb pta)
   *
  (forall (aa ab : Abstraction G vc),
      AlphaEqAbs aa ab -> AlphaEqAbs ab aa)
   *
  (forall (la lb : list (Abstraction G vc)),
      lAlphaEqAbs la lb -> lAlphaEqAbs lb la)).
Proof.
  intros. GAlphaInd; introns Hyp; intros; 
    try (econstructor; eauto; fail);[|].
- Case "termAbs".  eapply  alAbT with (lbnew := lbnew); eauto;
  [eauto with SetReasoning | repeat(disjoint_reasoning)].
- Case "patAbs".  eapply  alAbP with (lbnew := lbnew); eauto;
  [eauto with SetReasoning | repeat(disjoint_reasoning)].
Qed.



Lemma AlphaEqAbsTSameParam : forall (gsa gsb : GSym G)
  (lbva lbvb: list vcType)
  (tma : Term gsa) (tmb : Term gsb),
  AlphaEqAbs 
      (termAbs vc lbva tma) 
      (termAbs vc lbvb tmb)
  -> gsa =gsb.
Proof.
  introv Hal.
  inversion Hal.
  auto.
Qed.

Lemma AlphaEqAbsPSameParam : forall (gsa gsb : GSym G)
  (lbva lbvb: list vcType)
  (tma : Pattern gsa) (tmb : Pattern gsb),
  AlphaEqAbs 
      (patAbs vc lbva tma) 
      (patAbs vc lbvb tmb)
  -> gsa =gsb.
Proof.
  introv Hal.
  inversion Hal.
  auto.
Qed.

Lemma betterAbsTElim : forall (gs : GSym G)
  (lbva lbvb lvAvoid: list vcType)
  (tma tmb : Term gs),
  AlphaEqAbs 
      (termAbs vc lbva tma) 
      (termAbs vc lbvb tmb)
->{lbnew : list vcType $
      let swapa := combine lbva lbnew in
      let swapb := combine lbvb lbnew in
      length lbva = length lbnew #
      length lbvb = length lbnew #
      tFresh lbnew [tma, tmb] #
      (** naive elimination does not give the [lvAvoid] in the
         next hypothesis *)
      disjoint (lvAvoid++lbva++lbvb) lbnew #
      tAlphaEq vc (tSwap tma swapa) (tSwap tmb swapb)}.
Proof.
  introv Hab.
  inversion Hab. clear Hab.
  EqDecSndEq. subst.
  subst swapa. subst swapb.
  pose proof (GFreshDistRenWSpec vc lbnew 
              (tAllVars tma++tAllVars tmb++ 
                    lbnew ++lbva ++ lbvb++ lvAvoid))
    as Hfr.
  exrepnd. exists lvn. simpl.
  dands; try congruence; unfold tFresh;
  allsimpl; dands; repeat(disjoint_reasoning);[].
  rename X0 into Htal.
  apply (tcase alphaEquiVariant ) in Htal.
  specialize (Htal (combine lbnew lvn)).
  rewrite (tcase swap_app) in Htal.
  rewrite (tcase swap_app) in Htal.
  unfold tFresh in X.
  allsimpl. repnd.
  autorewrite with slow in Htal; try congruence;
  cpx; repeat (disjoint_reasoning).
Qed.

Lemma betterAbsPElim : forall (gs : GSym G)
  (lbva lbvb lvAvoid: list vcType)
  (tma tmb : Pattern gs),
  AlphaEqAbs
      (patAbs vc lbva tma) 
      (patAbs vc lbvb tmb)
->{lbnew : list vcType $
      let swapa := combine lbva lbnew in
      let swapb := combine lbvb lbnew in
      length lbva = length lbnew #
      length lbvb = length lbnew #
      pFresh lbnew [tma, tmb] #
      (** naive elimination does not give thhe next hypothesis *)
      disjoint (lvAvoid++lbva++lbvb) lbnew #
      pAlphaEq vc (pSwap tma swapa) (pSwap tmb swapb)}.
Proof.
  introv Hab.
  inversion Hab. clear Hab.
  EqDecSndEq. subst.
  subst swapa. subst swapb.
  pose proof (GFreshDistRenWSpec vc lbnew 
              (pAllVars tma++pAllVars tmb++ 
                    lbnew ++lbva ++ lbvb++ lvAvoid))
    as Hfr.
  exrepnd. exists lvn. simpl.
  dands; try congruence; unfold pFresh;
  allsimpl; dands; repeat(disjoint_reasoning);[].
  rename X0 into Htal.
  apply (tcase alphaEquiVariant ) in Htal.
  specialize (Htal (combine lbnew lvn)).
  rewrite (pcase swap_app) in Htal.
  rewrite (pcase swap_app) in Htal.
  unfold pFresh in X.
  allsimpl. repnd.
  autorewrite with slow in Htal; try congruence;
  cpx; repeat (disjoint_reasoning).
Qed.

Lemma alphaEqTransitive :
( 
  (forall (s : GSym G) ,
      transRel (@tAlphaEq _ vc s))
   *
  (forall (s : GSym G),
      transRel (@pAlphaEq _ vc s))
  *
      transRel (@AlphaEqAbs G vc)
  *
      transRel (@lAlphaEqAbs G vc)
).
Proof.
  intros.
  GAlphaInd; introns Hyp; intros; 
  allsimpl; trivial; try (econstructor; eauto; fail);
    [ | | | | | |].
- Case "tnode". inverts Hyp1.
  EqDecSndEq. subst.
  rename mb0 into mc.
  econstructor; eauto with slow.

- Case "pvleaf".  inverts Hyp.
  EqDecSndEq. subst.
  constructor.
  
- Case "pembed".  inverts Hyp1;
  EqDecSndEq; subst;
  econstructor; eauto with slow.

- Case "pnode". inverts Hyp1.
  EqDecSndEq. subst.
  rename mb0 into mc.
  econstructor; eauto with slow.

- Case "termAbs".
  destruct z as [ss lbvc tmc|];[|inversion Hyp5].
  duplicate Hyp5 as Htal.
  apply AlphaEqAbsTSameParam in Hyp5.
  symmetry in Hyp5. subst.
  apply (betterAbsTElim (lbnew ++ lbva++ (tAllVars tma))) in Htal.
  allsimpl. exrepnd.
  rename lbnew0 into lbcnew.
  (** we need to prepare lhs of [Htal0] so that it can match
    the inductive hypothessis [Hyp4].
    then we can undo the extra swappings done
    to rhs in this process *)
  apply (tcase alphaEquiVariant ) in Htal0.
  specialize (Htal0 (combine lbcnew lbnew)).
  rewrite (tcase swap_app) in Htal0.
  rewrite (tcase swap_app) in Htal0.
  unfold tFresh in Htal3.
  unfold tFresh in Hyp1.
  allsimpl. repnd.
  remAlphaRight Htal0 ll.
  autorewrite with slow in Htal0; try congruence;
  cpx; repeat (disjoint_reasoning).
  apply Hyp4 in Htal0.  subst.
  (* undo the changes done to RHS of [Htal0]*)
  apply (tcase alphaEquiVariant ) in Htal0.
  specialize (Htal0 (combine lbnew lbcnew)).
  remAlphaRight Htal0 ll.
  rewrite (tcase swap_app) in Htal0.
  autorewrite with slow in Htal0; try congruence;
  cpx; repeat (disjoint_reasoning).
  rewrite (tcase swap_app) in Heqll.
  rw <- app_assoc in Heqll.
  rewrite <- (tcase swap_app) in Heqll.
  rewrite <- (tcase swap_app) in Heqll.
  rewrite (tcase swapSwitch) in Heqll.
  rewrite <- AssociationList.ALSwitchCombine in Heqll.
  rewrite (tcase swapRevNoRep) in Heqll; auto;
  autorewrite with fast; cpx;[| disjoint_reasoning; fail].
  rewrite (tcase swap_app) in Heqll.
  rewrite (tcase swap_prop_s2Stronger) in Heqll.
  subst.
  apply alAbT with (lbnew:=lbcnew); try congruence;
  [unfolds_base; simpl; dands |]; cpx;
  repeat (disjoint_reasoning).
- Case "patAbs".
  destruct z as [|ss lbvc tmc];[inversion Hyp5|];[].
  duplicate Hyp5 as Htal.
  apply AlphaEqAbsPSameParam in Hyp5.
  symmetry in Hyp5. subst.
  apply (betterAbsPElim (lbnew ++ lbva++ (pAllVars tma))) in Htal.
  allsimpl. exrepnd.
  rename lbnew0 into lbcnew.
  (** we need to prepare lhs of [Htal0] so that it can match
    the inductive hypothessis [Hyp4].
    then we can undo the extra swappings done
    to rhs in this process *)
  apply (tcase alphaEquiVariant ) in Htal0.
  specialize (Htal0 (combine lbcnew lbnew)).
  rewrite (pcase swap_app) in Htal0.
  rewrite (pcase swap_app) in Htal0.
  unfold pFresh in Htal3.
  unfold pFresh in Hyp1.
  allsimpl. repnd.
  remAlphaRight Htal0 ll.
  autorewrite with slow in Htal0; try congruence;
  cpx; repeat (disjoint_reasoning).
  apply Hyp4 in Htal0.  subst.

  apply (tcase alphaEquiVariant ) in Htal0.
  specialize (Htal0 (combine lbnew lbcnew)).
  remAlphaRight Htal0 ll.
  rewrite (pcase swap_app) in Htal0.
  autorewrite with slow in Htal0; try congruence;
  cpx; repeat (disjoint_reasoning).
  rewrite (pcase swap_app) in Heqll.
  rw <- app_assoc in Heqll.
  rewrite <- (pcase swap_app) in Heqll.
  rewrite <- (pcase swap_app) in Heqll.
  rewrite (pcase swapSwitch) in Heqll.
  rewrite <- AssociationList.ALSwitchCombine in Heqll.
  rewrite (pcase swapRevNoRep) in Heqll; auto;
  autorewrite with fast; cpx;[| disjoint_reasoning; fail].
  rewrite (pcase swap_app) in Heqll.
  rewrite (pcase swap_prop_s2Stronger) in Heqll.
  subst.
  apply alAbP with (lbnew:=lbcnew); try congruence;
  [unfolds_base; simpl; dands |]; cpx;
  repeat (disjoint_reasoning).
- Case "laCons".  inverts Hyp3.
  subst. constructor; auto.
Qed.




(*
Lemma alphaEqSym : 
     (  (forall (s : GSym G) (ta tb : Term s)
        (lvA : list vcType),
            tAlphaEq lvA ta tb -> tAlphaEq lvA tb ta)
         *
        (forall (s : GSym G) (pta ptb : Pattern s)
        (lvA : list vcType),
            pAlphaEq lvA pta ptb -> pAlphaEq lvA ptb pta)
         *
        (forall (l : MixtureParam) (ma mb : Mixture l) 
        (lvA : list vcType)
        (lbva lbvb : list (list (vType vc))),
           lAlphaEqAbs lvA (MakeAbstractions ma lbva) 
                           (MakeAbstractions mb lbvb)
        -> lAlphaEqAbs lvA (MakeAbstractions mb lbvb) 
                           (MakeAbstractions ma lbva))).
Proof.
  GInductionS; introns Hyp; cpx; allsimpl;
  try (inversion Hyp; EqDecSndEq; subst; econstructor; eauto; fail);
  try (inversion Hyp0; EqDecSndEq; subst; inversion Hyp0;
  subst; EqDecSndEq; subst; econstructor; eauto; fail);[|].
- inversion Hyp1. EqDecSndEq. subst. econstructor; eauto.
  inversion X. subst. subst swapa. subst swapb.
  EqDecSndEq. subst. econstructor; eauto.
  + eauto with SetReasoning.
  + apply Hyp; auto; autorewrite with fast. auto.
  + inversion mb. subst. destruct mb;
    inverts H. subst. duplicate X0 as XX.
    inversion X0;subst; cpx.


(* apply Hyp0.


apply Hyp0. 
- inversion Hyp1. EqDecSndEq. subst. econstructor; eauto.
  inversion X. subst. subst swapa. subst swapb.
  EqDecSndEq. subst. econstructor; eauto.
  + eauto with SetReasoning.
  + apply Hyp; auto; autorewrite with fast. auto.
Qed.
*)

Abort.
*)


Lemma eqset_subtractv_if_left :
  forall l l1 l2,
    eqset l1 l2 -> eqset (@subtractv G vc l1 l) (subtractv l2 l).
Proof.
  unfold subtractv.
  apply eqset_diff_if_left.
Qed.

Lemma eqset_subtractv_if_right :
  forall l l1 l2,
    eqset l1 l2 -> eqset (@subtractv G vc l l1) (subtractv l l2).
Proof.
  unfold subtractv.
  apply eqset_diff_if_right.
Qed.

Lemma eq_subtractv_if_left :
  forall l l1 l2,
    l1 = l2 -> @subtractv G vc l1 l = subtractv l2 l.
Proof.
  sp; subst; sp.
Qed.

Lemma eq_subtractv_if_right :
  forall l l1 l2,
    l1 = l2 -> @subtractv G vc l l1 = subtractv l l2.
Proof.
  sp; subst; sp.
Qed.

Lemma subtractv_nil :
  forall l,
    @subtractv G vc l [] = l.
Proof.
  unfold subtractv; sp.
Qed.

Lemma subtractv_nil_l :
  forall l,
    @subtractv G vc [] l = [].
Proof.
  unfold subtractv; sp.
  rw diff_nil; auto.
Qed.

Lemma subtractv_app_l :
  forall l1 l2 l,
    @subtractv G vc (l1 ++ l2) l = subtractv l1 l ++ subtractv l2 l.
Proof.
  unfold subtractv; introv.
  rw diff_app_r; auto.
Qed.

Definition freevars_abs (a : Abstraction G vc) :=
  match a with
    | termAbs _ vars t => subtractv (tfreevars vc t) vars
    | patAbs  _ vars p => subtractv (pfreevars vc p) vars
  end.

Fixpoint freevars_labs (l : list (Abstraction G vc)) :=
  match l with
    | [] => []
    | a :: l => freevars_abs a ++ freevars_labs l
  end.






(* bad duplicate: this equality holds unconditionally
    see freevarsEquivariant in SwapProps.v*)
Lemma freevars_swap_eq :
  (
    (forall (gs : GSym G) (t : Term gs),
     forall (l1 l : list vcType),
       length l1 = length l
       -> disjoint l1 l
       -> tFresh l [t]
       -> tfreevars vc (tSwap t (combine l1 l))
          = swapLVar (combine l1 l) (tfreevars vc t))
    *
    (forall (gs : GSym G) (p : Pattern gs),
     forall (l1 l : list vcType),
       length l1 = length l
       -> disjoint l1 l
       -> pFresh l [p]
       -> pfreevars vc (pSwap p (combine l1 l))
          = swapLVar (combine l1 l) (pfreevars vc p))
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) lbvars,
     forall (l1 l : list vcType),
       length l1 = length l
       -> disjoint l1 l
       -> mFresh l [m]
       -> mfreevars vc (mSwap m (combine l1 l)) (swapLLVar (combine l1 l) lbvars)
          = swapLVar (combine l1 l) (mfreevars vc m lbvars))
  ).
Proof.
  GInduction; auto; introv;
  try (complete (allsimpl; cpx));
  try (complete (allsimpl; introv f e; DDeqs; cpx; rw subtractv_nil_l; auto)).

  - Case "tnode".
    allsimpl.
    introv M len disj f.
    unfold allBndngVars.
    rewrite lBoundVars_swap.
    rw M; auto.

  - Case "pnode".
    allsimpl.
    introv M len disj f.
    apply (M []); auto.

  - Case "mtcons".
    allsimpl.
    introv T M len disj f.
    destruct lbvars; simpl;
    rewrite swapLVar_app;
    apply app_if.

    + apply T; auto;
      try (complete (unfold mFresh in f; unfold mFresh, tFresh;
                     allsimpl; allrw disjoint_app_r; sp)).

    + apply (M []); auto;
      try (complete (unfold mFresh in f; unfold mFresh;
                     allsimpl; allrw disjoint_app_r; sp)).

    + rewrite swapLVar_subtractv.
      rw T; auto;
      try (complete (unfold mFresh in f; unfold mFresh, tFresh;
                     allsimpl; allrw disjoint_app_r; sp)).

    + apply M; auto;
      try (complete (unfold mFresh in f; unfold mFresh;
                     allsimpl; allrw disjoint_app_r; sp)).

  - Case "mpcons".
    allsimpl.
    introv P M len disj f.
    destruct lbvars; simpl;
    rewrite swapLVar_app;
    apply app_if.

    + apply P; auto;
      try (complete (unfold mFresh in f; unfold mFresh, pFresh;
                     allsimpl; allrw disjoint_app_r; sp)).

    + apply (M []); auto;
      try (complete (unfold mFresh in f; unfold mFresh;
                     allsimpl; allrw disjoint_app_r; sp)).

    + rewrite swapLVar_subtractv.
      rw P; auto;
      try (complete (unfold mFresh in f; unfold mFresh, pFresh;
                     allsimpl; allrw disjoint_app_r; sp)).

    + apply M; auto;
      try (complete (unfold mFresh in f; unfold mFresh;
                     allsimpl; allrw disjoint_app_r; sp)).
Qed.


Lemma tFresh_app :
  forall g l (l1 l2 : list (Term g)),
    @tFresh G vc g l (l1 ++ l2) <=> (tFresh l l1 # tFresh l l2).
Proof.
  introv.
  unfold tFresh.
  rw flat_map_app.
  rw disjoint_app_r.
  split; sp.
Qed.

Lemma pFresh_app :
  forall g l (l1 l2 : list (Pattern g)),
    @pFresh G vc g l (l1 ++ l2) <=> (pFresh l l1 # pFresh l l2).
Proof.
  introv.
  unfold pFresh.
  rw flat_map_app.
  rw disjoint_app_r.
  split; sp.
Qed.


(* duplicate *)
Lemma swapVar_unchanged :
  forall v l1 l2,
    !LIn v l1
    -> !LIn v l2
    -> @swapVar G vc (combine l1 l2) v = v.
Proof.
  induction l1; introv ni1 ni2; allsimpl; auto.
  allrw not_over_or; repnd.
  destruct l2; allsimpl; auto.
  allrw not_over_or; repnd.
  DDeqs; sp.
Qed.
(* duplicate *)
Lemma swapVar_in :
  forall l1 l2 v,
    LIn v l1
    -> disjoint l1 l2
    -> length l1 = length l2
    -> no_repeats l2
    -> LIn (@swapVar G vc (combine l1 l2) v) l2.
Proof.
  induction l1 as [|x1 l1]; introv i1 disj len norep; allsimpl; tcsp.
  destruct l2 as [|x2 l2]; allsimpl; cpx.
  allrw disjoint_cons_l; allrw disjoint_cons_r; repnd; allsimpl.
  allrw not_over_or; repnd.
  allrw no_repeats_cons; repnd.
  DDeqs; sp; GC; rw (swapVar_unchanged x2); auto.
Qed.

Lemma eq_subtractv :
  forall vs1 vs2 l1 l2 l,
    disjoint l vs1
    -> disjoint l vs2
    -> disjoint l l1
    -> disjoint l l2
    -> length l = length l1
    -> length l = length l2
    -> no_repeats l
    -> @swapLVar G vc (combine l1 l) vs1 = swapLVar (combine l2 l) vs2
    -> subtractv vs1 l1 = subtractv vs2 l2.
Proof.
  induction vs1; introv disj1 disj2 disj3 disj4 len1 len2 norep e;
  allsimpl; destruct vs2; allsimpl;
  allrw subtractv_nil; allrw subtractv_nil_l; auto; inj.
  allapply cons_inj; repnd.
  repeat (rewrite subtractv_cons).
  allrw disjoint_cons_r; repnd.
  DDeqs; try (complete (eapply IHvs1; eauto)).

  - rw (swapVar_unchanged v) in e0; auto.

    pose proof (@swapVar_in l1 l a) as h;
      repeat (autodimp h hyp);
      try (complete (apply disjoint_sym; auto)).
    rw e0 in h; sp.

  - rw (swapVar_unchanged a) in e0; auto.

    pose proof (@swapVar_in l2 l v) as h;
      repeat (autodimp h hyp);
      try (complete (apply disjoint_sym; auto)).
    rw <- e0 in h; sp.

  - rw (swapVar_unchanged v) in e0; auto.
    rw (swapVar_unchanged a) in e0; auto.
    subst.
    apply eq_cons; auto.
    apply IHvs1 with (l := l); auto.
Qed.

Lemma freevars_in_allvars :
  (
    (forall (gs : GSym G) (t : Term gs),
       subset (tfreevars vc t) (tAllVars t))
    *
    (forall (gs : GSym G) (p : Pattern gs),
       subset (pfreevars vc p) (pAllVars p))
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) lbvars,
       subset (mfreevars vc m lbvars) (mAllVars m))
  ).
Proof.
  GInduction; auto; introv;
  try (complete (allsimpl; cpx));
  try (complete (allsimpl; introv f e; DDeqs; cpx; rw subtractv_nil_l; auto)).

  - Case "mtcons".
    allsimpl.
    introv ss M; introv.
    destruct lbvars; allsimpl; apply subset_app_lr; auto.
    unfold subtractv.
    apply subset_diff.
    apply subset_app_r; auto.

  - Case "mpcons".
    allsimpl.
    introv ss M; introv.
    destruct lbvars; allsimpl; apply subset_app_lr; auto.
    unfold subtractv.
    apply subset_diff.
    apply subset_app_r; auto.
Qed.

Lemma alpha_preserves_free_vars :
  (
    (forall (s : GSym G) (t1 t2 : Term s),
       tAlphaEq vc t1 t2 -> tfreevars vc t1 = tfreevars vc t2)
    *
    (forall (s : GSym G) (p1 p2 : Pattern s),
       pAlphaEq vc p1 p2 -> pfreevars vc p1 = pfreevars vc p2)
    *
    (forall a1 a2,
       AlphaEqAbs a1 a2 -> freevars_abs a1 = freevars_abs a2)
    *
    (forall l1 l2,
       lAlphaEqAbs l1 l2 -> freevars_labs l1 = freevars_labs l2)
  ).
Proof.
  intros.
  GAlphaInd; introns Hyp; intros;
  try (complete (allsimpl; auto; ddeq; auto)).

  - Case "tnode".
    allsimpl.
    allunfold MakeAbstractionsTNode.
    allunfold MakeAbstractionsTNodeAux.
    clear Hyp.

    assert (forall ma : Mixture (tpRhsAugIsPat p),
              freevars_labs
                (MakeAbstractions vc ma
                                  (lBoundVars vc (bndngPatIndices p) ma))
              = mfreevars vc ma (lBoundVars vc (bndngPatIndices p) ma)) as eqs.
    (* begin proof of assert *)
    clear ma mb Hyp0.
    introv.
    remember (lBoundVars vc (bndngPatIndices p) ma); clear Heql.
    revert l.
    induction ma; introv; simpl; auto.
    destruct l; allsimpl.
    rw subtractv_nil; apply app_if; auto.
    apply app_if; auto.
    destruct l; allsimpl.
    rw subtractv_nil; apply app_if; auto.
    apply app_if; auto.
    (* end proof of assert *)

    repeat (rw <- eqs); auto.

  - Case "pnode".
    allsimpl.
    allunfold MakeAbstractionsPNode.
    clear Hyp.

    assert (forall ma : Mixture (map (fun x : GSym G => (true, x)) (ppRhsSym p)),
              freevars_labs (MakeAbstractions vc ma [])
              = mfreevars vc ma []) as eqs.
    (* begin proof of assert *)
    clear ma mb Hyp0.
    introv.
    induction ma; introv; simpl; auto.
    rw subtractv_nil; apply app_if; auto.
    apply app_if; auto.
    (* end proof of assert *)

    repeat (rw <- eqs); auto.

  - Case "termAbs".
    allsimpl.
    allrw disjoint_app_l; repnd.
    rw two_as_app in Hyp1.
    apply tFresh_app in Hyp1; repnd.
    repeat (rw (fst (fst freevars_swap_eq)) in Hyp4; auto).

    apply eq_subtractv with (l := lbnew); auto;
    try (complete (apply disjoint_sym; auto));
    unfold tFresh in Hyp1; unfold tFresh in Hyp6; repnd; auto;
    allrw disjoint_flat_map_r;
    pose proof (Hyp7 tmb) as h1; simpl in h1; autodimp h1 hyp;
    pose proof (Hyp8 tma) as h2; simpl in h2; autodimp h2 hyp.

    pose proof (fst (fst freevars_in_allvars) gs tma) as h.
    apply subset_disjoint_r with (l2 := tAllVars tma); auto.

    pose proof (fst (fst freevars_in_allvars) gs tmb) as h.
    apply subset_disjoint_r with (l2 := tAllVars tmb); auto.

  - Case "patAbs".
    allsimpl.
    allrw disjoint_app_l; repnd.
    rw two_as_app in Hyp1.
    apply pFresh_app in Hyp1; repnd.
    repeat (rw (snd (fst freevars_swap_eq)) in Hyp4; auto).

    apply eq_subtractv with (l := lbnew); auto;
    try (complete (apply disjoint_sym; auto));
    unfold pFresh in Hyp1; unfold pFresh in Hyp6; repnd; auto;
    allrw disjoint_flat_map_r;
    pose proof (Hyp7 tmb) as h1; simpl in h1; autodimp h1 hyp;
    pose proof (Hyp8 tma) as h2; simpl in h2; autodimp h2 hyp.

    pose proof (snd (fst freevars_in_allvars) gs tma) as h.
    apply subset_disjoint_r with (l2 := pAllVars tma); auto.

    pose proof (snd (fst freevars_in_allvars) gs tmb) as h.
    apply subset_disjoint_r with (l2 := pAllVars tmb); auto.

  - Case "laCons".
    allsimpl.
    apply app_if; auto.
Qed.





Ltac dvlin v l := destruct (in_deq _ (DeqVtype vc) v l).

(* duplicate : do SearchAbout tFresh app *)
Lemma tFresh_app_l :
  forall g l1 l2 ts,
    @tFresh G vc g (l1 ++ l2) ts
    <=>
    (tFresh l1 ts # tFresh l2 ts # disjoint l1 l2 # no_repeats l1 # no_repeats l2).
Proof.
  unfold tFresh; introv.
  rw disjoint_app_l.
  rw no_repeats_app; split; sp.
Qed.


Lemma simple_combine_app_app :
  forall T (l1 l2 l3 l4 : list T),
    length l1 = length l3
    -> combine (l1 ++ l2) (l3 ++ l4)
       = combine l1 l3 ++ combine l2 l4.
Proof.
  induction l1; simpl; introv len; destruct l3; allsimpl; cpx.
  rw IHl1; sp.
Qed.



End AlphaProps.

Lemma tAlphaEqTransEauto:
 forall 
  {G : CFGV} {vc : VarSym G}
   (s : GSym G) (a b c : Term s),
   tAlphaEq vc a b
   -> tAlphaEq vc b c
   -> tAlphaEq vc a c.
Proof.
  introns Hyp.
  pose proof (@alphaEqTransitive G vc) as Hpr.
  repnd. unfold transRel in Hpr2.
  eauto.
Qed.
  
Lemma pAlphaEqTransEauto:
 forall 
  {G : CFGV} {vc : VarSym G}
   (s : GSym G) (a b c : Pattern s),
   pAlphaEq vc a b
   -> pAlphaEq vc b c
   -> pAlphaEq vc a c.
Proof.
  introns Hyp.
  pose proof (@alphaEqTransitive G vc) as Hpr.
  repnd. unfold transRel in Hpr1.
  eauto.
Qed.


Definition ALtcase 
  {A B C D} (t:A*B*C*D) : A
  := fst (fst (fst t)).

Definition ALpcase 
  {A B C D} (t:A*B*C*D) : B
  := snd (fst (fst t)).

Definition Abcase 
  {A B C D} (t:A*B*C*D) : C
  := (snd (fst t)).

Definition LAbcase 
  {A B C D} (t:A*B*C*D) : D
  := ((snd t)).



Hint Resolve
(tcase alphaEqRefl)
(pcase alphaEqRefl)
(mcase alphaEqRefl)
  (ALtcase alphaEqSym)
  (ALpcase alphaEqSym)
  (Abcase alphaEqSym)
  (LAbcase alphaEqSym)
  AlphaEqNilAbsT
  AlphaEqNilAbsP
  tAlphaEqTransEauto
  pAlphaEqTransEauto : Alpha.


Lemma pAlphaSwapEmSwap
 : forall {G : CFGV} {vc : VarSym G},
(  (forall (s : GSym G) (ta : Term s), True)
   *
  (forall (s : GSym G) (pta : Pattern s)
  (sw : Swapping vc),
      pAlphaEq vc (pSwapEmbed pta sw)
                  (pSwap pta sw))
   *
  (forall (mp : MixtureParam) (ma: Mixture mp)
  (llbv : list (list (vType vc)))
  (sw : Swapping vc),
  (forall b s, LIn (b,s) mp -> b= true)
   -> lAlphaEqAbs (MakeAbstractions vc (mSwapEmbed ma sw) llbv) 
                (MakeAbstractions vc (mSwap ma sw) llbv))).
Proof.
intros. 
GInduction; cpx; allsimpl;
  try (econstructor; eauto with Alpha; fail).
- Case "pnode". introns Hyp.
  allsimpl. constructor.
  unfold MakeAbstractionsPNode.  
  apply Hyp.
  introv Hin.
  apply in_map_iff in Hin; exrepnd; cpx.
- Case "mtcons". introns Hyp.
   pose proof (Hyp1 _ _ (inl eq_refl)). cpx.
Qed.


(** swapping by swapping that leaves the
    free vars unchanged results in an alpha equal term.
    A swapping with whose both domain and range
    are disjoint from freevars can be used *)
Lemma alphaEqSwapNonFree : forall {G : CFGV} {vc : VarSym G},
(  (forall (s : GSym G) (t : Term s) (sw : Swapping vc),
      leavesLVarUnchanged sw (tfreevars vc t)
      -> tAlphaEq vc t (tSwap t sw))
   *
  (forall (s : GSym G) (pt : Pattern s) (sw : Swapping vc),
     leavesLVarUnchanged sw (pfreevars vc pt)
      -> pAlphaEq vc pt (pSwap pt sw))
   *
  (forall (l : MixtureParam) (m : Mixture l) (sw : Swapping vc)
  (lbv : list (list (vType vc))),
      leavesLVarUnchanged sw (mfreevars vc m lbv)
      -> lAlphaEqAbs 
            (MakeAbstractions vc m lbv)
            (MakeAbstractions vc (mSwap m sw) (swapLLVar sw lbv)))).
Proof.
  intros.
  GInduction; introns Hyp; intros; cpx; allsimpl;
  try dlist_len lbv;  try (econstructor; eauto with slow; fail).

- Case "vleaf".
  rewrite DeqSym.
  ddeq; sp;[| eauto with Alpha; fail].
  destruct e. allsimpl.
  repeat (disjoint_reasoning).
  rewrite Hyp; cpx.
  eauto 1 with Alpha.

- Case "tnode". constructor. allunfold mAlphaEq.
  unfold MakeAbstractionsTNode.
  unfold MakeAbstractionsTNodeAux.
  unfold allBndngVars.
   rewrite <- lBoundVars_equivariant.
  cpx.

- Case "pnode". constructor. allunfold mAlphaEq.
  unfold MakeAbstractionsPNode.
  specialize (Hyp sw nil).
  simpl in Hyp. cpx.

- Case "mtcons". destruct lbv; cpx;
  apply lforallApp in Hyp1; repnd;
  [ allsimpl; specialize (Hyp0 sw []); simpl in Hyp0;
    constructor; cpx ; 
     apply AlphaEqNilAbsT;
      apply Hyp; cpx|].

    constructor; cpx.
  allsimpl. 
  pose proof  (GFreshDistRenWSpec vc l
            (tAllVars ph++tAllVars  (tSwap ph sw)++ 
              (swapLVar sw l)++ l ++ (tfreevars vc ph)++
                  ALDom sw ++ ALRange sw ++ l))
      as Hfr.
  exrepnd.
  apply alAbT with (lbnew:=lvn); 
    try (unfold swapLVar ; autorewrite with fast;
      congruence; fail);
  [unfolds_base; simpl; dands | | ]; cpx;
  try (autorewrite with fast;
  repeat (disjoint_reasoning); fail);[].
  autorewrite with SwapAppR.
  assert (lvn = swapLVar sw lvn ) as XX by
    (symmetry; apply swapLVarNoChange;
        repeat (disjoint_reasoning)).

  remember (combine l lvn) as swt.
  rewrite XX.
  unfold swapLVar. rewrite <- map_combine.
  fold (swapSwap sw (combine l lvn)).
  rewrite <- (tcase swap_prop_e1Stronger).
  subst swt.
  apply tAlphaEqEquivariantRev with 
    (sw0:=rev (combine l lvn)).
  autorewrite with SwapAppR.
  autorewrite with fast.
  apply Hyp.
  intros v Hin.
  unfolds_base.
  autorewrite with SwapAppL.
  assert (disjoint l lvn) as Xd by repeat(disjoint_reasoning).
  destruct (in_deq _ (DeqVtype vc) v l) as [Xin | Xnot].
  + dimp (@swapVar_in G vc l lvn v); cpx.
    remember (swapVar (combine l lvn) v) as vs.
    assert (leavesLVarUnchanged sw lvn)  as Xun by
    (apply leavesLVarUnchanged1;repeat (disjoint_reasoning)).
    apply Xun in hyp.
    repnud hyp. rw hyp. subst vs.
    autorewrite with SwapAppR.
    autorewrite with fast. refl.
  + assert (disjoint (tfreevars vc ph) lvn) as Hdiss by
      repeat (disjoint_reasoning).
    assert (LIn v (tfreevars vc ph -- l)) as Hins by
    (apply in_diff; dands; cpx).
    apply Hdiss in Hin.
    pattern ((swapVar (combine l lvn) v)).
    rewrite swapVarNoChange; cpx;
    autorewrite with fast; try congruence.
    apply Hyp2 in Hins.
    rewrite Hins. apply swapVarNonChangeRev.
    rewrite swapVarNoChange; cpx;
    autorewrite with fast; try congruence.

(** exactly same as [mtcons] case *)
- Case "mpcons". destruct lbv; cpx;
  apply lforallApp in Hyp1; repnd;
  [ allsimpl; specialize (Hyp0 sw []); simpl in Hyp0;
    constructor; cpx ; 
     apply AlphaEqNilAbsP;
      apply Hyp; cpx|].

    constructor; cpx.
  allsimpl. 
  pose proof  (GFreshDistRenWSpec vc l
            (pAllVars ph++pAllVars  (pSwap ph sw)++ 
              (swapLVar sw l)++ l ++ (pfreevars vc ph)++
                  ALDom sw ++ ALRange sw ++ l))
      as Hfr.
  exrepnd.
  apply alAbP with (lbnew:=lvn); 
    try (unfold swapLVar ; autorewrite with fast;
      congruence; fail);
  [unfolds_base; simpl; dands | | ]; cpx;
  try (autorewrite with fast;
  repeat (disjoint_reasoning); fail);[].
  autorewrite with SwapAppR.
  assert (lvn = swapLVar sw lvn ) as XX by
    (symmetry; apply swapLVarNoChange;
        repeat (disjoint_reasoning)).

  remember (combine l lvn) as swt.
  rewrite XX.
  unfold swapLVar. rewrite <- map_combine.
  fold (swapSwap sw (combine l lvn)).
  rewrite <- (pcase swap_prop_e1Stronger).
  subst swt.
  apply pAlphaEqEquivariantRev with 
    (sw0:=rev (combine l lvn)).
  autorewrite with SwapAppR.
  autorewrite with fast.
  apply Hyp.
  intros v Hin.
  unfolds_base.
  autorewrite with SwapAppL.
  assert (disjoint l lvn) as Xd by repeat(disjoint_reasoning).
  destruct (in_deq _ (DeqVtype vc) v l) as [Xin | Xnot].
  + dimp (@swapVar_in G vc l lvn v); cpx.
    remember (swapVar (combine l lvn) v) as vs.
    assert (leavesLVarUnchanged sw lvn)  as Xun by
    (apply leavesLVarUnchanged1;repeat (disjoint_reasoning)).
    apply Xun in hyp.
    repnud hyp. rw hyp. subst vs.
    autorewrite with SwapAppR.
    autorewrite with fast. refl.
  + assert (disjoint (pfreevars vc ph) lvn) as Hdiss by
      repeat (disjoint_reasoning).
    assert (LIn v (pfreevars vc ph -- l)) as Hins by
    (apply in_diff; dands; cpx).
    apply Hdiss in Hin.
    pattern ((swapVar (combine l lvn) v)).
    rewrite swapVarNoChange; cpx;
    autorewrite with fast; try congruence.
    apply Hyp2 in Hins.
    rewrite Hins. apply swapVarNonChangeRev.
    rewrite swapVarNoChange; cpx;
    autorewrite with fast; try congruence.
Qed.

Lemma freeVarsSuppAux:
forall {G : CFGV} {vc : VarSym G},
((forall (s : GSym G) (t : Term s),
    forall v, ! LIn v (tfreevars vc t)
      -> (finite 
             (fun b => !(tAlphaEq vc t 
                              (tSwap t [(v,b)])))))).
Proof.
  introv Hin.
  exists (tfreevars vc t).
  introv Hntal.
  destruct (in_deq _ (DeqVtype vc) a 
    (tfreevars vc t)) as [ ? | Hneq]; cpx.
  provefalse.
  apply Hntal.
  apply (tcase alphaEqSwapNonFree).
  apply leavesLVarUnchanged1.
  allsimpl. repeat (disjoint_reasoning); cpx.
Qed.

Lemma freeVarsSuppAux2:
forall {G : CFGV} {vc : VarSym G},
((forall (s : GSym G) (t : Term s),
    forall v, LIn v (tfreevars vc t)
      -> ! (finite 
             (fun b => !(tAlphaEq vc t 
                              (tSwap t [(v,b)])))))).
Proof.
  introv Hin. introv Hc.
  repnud Hc.
  exrepnd.
  pose proof (vFreshVarSpec
      ([v]++la ++ (tfreevars vc t)) v) as XX.
  remember (vFreshVar ([v]++la ++ tfreevars vc t) v) as vn.
  clear Heqvn.
  rw in_app_iff in XX.
  rw in_app_iff in XX.
  apply XX. right. left.
  apply Hc0. introv Hal.
  apply (ALtcase alpha_preserves_free_vars) in Hal.
  rewrite Hal in Hin. clear Hal.
  rewrite <- (tcase freevarsEquivariant) in Hin.
  rw in_map_iff in Hin.
  exrepnd.
  pose proof (swapVarInOrEq2 [(v,vn)] a) as Hs.
  rewrite <- Hin0 in Hs.
  clear Hin0.
  dimp Hs; simpl; cpx; try (constructor; auto; cpx; fail);

  [|]; cpx;
  repeat (disjoint_reasoning);cpx.
  introv Hc. dorn Hc; cpx.
  subst. clear Hs. 
  apply XX. cpx.
Qed.

Lemma freeVarsSupp:
forall {G : CFGV} {vc : VarSym G},
((forall (s : GSym G) (t : Term s),
    forall v, LIn v (tfreevars vc t)
      <=> !(finite 
             (fun b => !(tAlphaEq vc t 
                              (tSwap t [(v,b)])))))).
Proof.
  intros. split.
  - apply freeVarsSuppAux2.
  - introv Hin. destruct (in_deq _ (DeqVtype vc) v
    (tfreevars vc t)) as [ ? | Hneq]; cpx.
    provefalse. apply Hin.
    apply freeVarsSuppAux.
    trivial.
Qed.


(*
   
(forall (s : GSym G) (pt : Pattern s) (sw : Swapping vc),
  forall v, LIn v (pfreevars vc pt)
    <=> !(finite 
           (fun b => !(pAlphaEq vc pt 
                            (pSwap pt [(v,b)])))))
   *
(forall (l : MixtureParam) (m : Mixture l) (sw : Swapping vc)
  (lbv : list (list (vType vc))),
  forall v, LIn v (mfreevars vc m lbv)
    <=> !(finite 
           (fun b => !(mAlphaEq vc m 
                            (mSwap m [(v,b)])))))
.

*)
