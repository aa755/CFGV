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

Require Export SubstAux.
Require Export AlphaEqProps.




Definition genPatSwapping
   {G : CFGV} {vc : VarSym G}
  {lgs : list (bool * GSym G)} (pts : Mixture lgs)
   (lvAvoid : list (vType vc))
  : list (Swapping vc) :=
    let toRen :=  
    map (lvKeep lvAvoid) (LLBinders vc pts)  in
    vFreshDistRenLL vc toRen (lvAvoid++(mAllVars pts)).

Lemma genPatSwappingSpec : forall
   {G : CFGV} {vc : VarSym G}
  {lgs : list (bool * GSym G)} (pts : Mixture lgs)
   (lvAvoid : list (vType vc)),
  let lswap := genPatSwapping pts lvAvoid in
  length lswap = length lgs
  # no_repeats (flat_map (@ALRange _ _) lswap)
  # disjoint (flat_map (@ALRange _ _) lswap) 
             (lvAvoid++(mAllVars pts)).
Proof.
  intros. subst lswap. unfold genPatSwapping.
  unfold vFreshDistRenLL.
  AddFDLLSpec. repnd.
  unfold LLBinders in FdSpec.
  apply (f_equal (@length _)) in FdSpec.
  autorewrite with fast in FdSpec.
  dands; cpx.
Qed.

Ltac AddFDLLSpec2 :=
  let FdSpec := fresh "FdSpec" in 
  let FdLL := fresh "FdLL" in 
  match goal with
  [ |- context [FreshDistinctRenListList ?ft ?llv ?lvA] ]
    => pose proof (FreshDistRenLLSpec2 ft llv lvA) as FdSpec;
        simpl in FdSpec;
     remember (FreshDistinctRenListList ft llv lvA) as FdLL

  end.


Lemma genPatSwappingSpec2 : forall
   {G : CFGV} {vc : VarSym G}
  {lgs : list (bool * GSym G)} (pts : Mixture lgs)
   (lvAvoid : list (vType vc)),
  let lswap := genPatSwapping pts lvAvoid in
  disjoint (flat_map (@ALDom _ _) lswap) 
            (flat_map (@ALRange _ _) lswap).
Proof.
  intros. subst lswap. unfold genPatSwapping.
  unfold vFreshDistRenLL.
  AddFDLLSpec2.
  repnd; cpx.
  SetReasoning.
  apply subset_eq in FdSpec.
  eapply subset_trans; eauto.
  clear FdSpec FdSpec1 FdSpec2 FdSpec0 HeqFdLL FdLL.
  induction pts; allsimpl; cpx.
  - unfold LLBinders in IHpts.
    introv Hc.
    apply IHpts in Hc.
    allrw in_app_iff; cpx.
  - unfold LLBinders in IHpts.
    introv Hc. allrw in_app_iff.
    dorn Hc; cpx.
    + right. left. 
      apply (pcase (bindersAllvarsSubset G vc)).
      unfold lvKeep in Hc.
      eauto 3 with SetReasoning.
    + apply IHpts in Hc.
      allrw in_app_iff; cpx.
Qed.


Lemma disjointlforall : forall
   {G : CFGV} {vc : VarSym G}
   (lswap : list (Swapping vc)),
  disjoint (flat_map (@ALDom _ _) lswap) 
            (flat_map (@ALRange _ _) lswap)
   -> lForall (fun x => disjoint (ALDom x) (ALRange x)) lswap.
Proof.
  induction lswap; cpx; introv Hdis.
  allsimpl.
  repeat (disjoint_reasoning); cpx.
Qed.

Lemma genPatSwappingSpec3 : forall
   {G : CFGV} {vc : VarSym G}
  {lgs : list (bool * GSym G)} (pts : Mixture lgs)
   (lvAvoid : list (vType vc)),
  let lswap := genPatSwapping pts lvAvoid in
  lForall (fun x => disjoint (ALDom x) (ALRange x)) lswap.
Proof.
  intros.
  apply  disjointlforall.
  subst lswap.
  apply genPatSwappingSpec2.
Qed.

Lemma genPatSwappingSpec4 : forall
   {G : CFGV} {vc : VarSym G}
  {lgs : list (bool * GSym G)} (pts : Mixture lgs)
   (lvAvoid : list (vType vc)),
  let lswap := genPatSwapping pts lvAvoid in
  map (@ALDom _ _) lswap= 
    map (lvKeep lvAvoid) (LLBinders vc pts).
Proof.
  intros.
  subst lswap.
  unfold genPatSwapping. 
  unfold vFreshDistRenLL.
  AddFDLLSpec.
  repnd. dands; auto.
Qed.
  
Lemma genPatSwappingSpec5 : forall
   {G : CFGV} {vc : VarSym G}
  {lgs : list (bool * GSym G)} 
   (lvAvoid : list (vType vc))
    (pts : Mixture lgs)
    (lswap : list (Swapping vc)),
  map (@ALDom _ _) lswap= 
    map (lvKeep lvAvoid) (LLBinders vc pts)
  -> liftRelPtwise (fun _ _ _ => True) 
          (fun s pt sw => 
              subset (lvKeep lvAvoid (pBndngVars vc pt)) (ALDom sw))
              pts lswap.
Proof.
  unfold LLBinders.
  induction pts; introv Hmeq; 
  destruct lswap as [| sh stl];  cpx.
  - allsimpl. dands; trivial.
    inverts Hmeq.
    rw H0 in H1.
    apply IHpts; cpx.
  - allsimpl. inverts Hmeq. dands; trivial; eauto.
Qed.

Definition genTermSwapping 
   {G : CFGV} {vc : VarSym G}
   (lln : list (list nat) )
   (patSwaps : list (Swapping vc))
  : list (Swapping vc) :=
map (flat_map (fun n=> nth n patSwaps [])) lln.

(*
Definition pSwap := 2.
Definition mSwap := 2.
Definition tSSubstAux :=2.
Definition pSSubstAux :=2.
Definition mSSubstAux :=2.
*)

Fixpoint pSwapBindEmbed
       {G  : CFGV}
       {vc : VarSym G}
       {gs : GSym G}
       (pt : Pattern gs)
       (swBind swEmbed  : Swapping vc) {struct pt} : Pattern gs  :=
  match pt with
    | ptleaf a v => ptleaf a v
    | pvleaf vcc var =>
      pvleaf vcc (match DeqVarSym vc vcc with
                    | left eqq => swapVar (transport eqq swBind) var
                    | right _ => var
                  end)
    | pnode p lpt => pnode p (mSwapBindEmbed lpt swBind swEmbed)
    | embed p nt => embed p (tSwap nt swEmbed)
  end
with mSwapBindEmbed
       {G  : CFGV}
       {vc : VarSym G}
       {lgs : list (bool * GSym G)}
       (pts : Mixture lgs)
       (swBind swEmbed : Swapping vc)
       {struct pts}
     : Mixture lgs  :=
  match pts in Mixture lgs return Mixture lgs with
    | mnil  => mnil
   (** will not happen *)
    | mtcons _ _ ph ptl => mtcons ph (mSwapBindEmbed ptl swBind swEmbed)
    | mpcons _ _ ph ptl =>
           mpcons (pSwapBindEmbed ph swBind swEmbed) 
                  (mSwapBindEmbed ptl swBind swEmbed)
  end.

Fixpoint mSwapTermPat
       {G  : CFGV}
       {vc : VarSym G}
       {lgs : list (bool * GSym G)}
       (pts : Mixture lgs)
       (swPat swTerm : list (Swapping vc))
       {struct pts}
     : Mixture lgs  :=
match pts with
| mnil => mnil
| mtcons _ _ th ttl => 
    mtcons (tSwap th (lhead swTerm))
           (mSwapTermPat ttl (tail swPat) (tail swTerm))
| mpcons _ _ ph ptl => 
    mpcons (pSwapBindEmbed ph (lhead swPat) (lhead swTerm))
           (mSwapTermPat ptl (tail swPat) (tail swTerm))
end.

(** this definition might seem like a waste of space.
  [nodeRenAlpha] just instantiatess
  [lln] with [(bndngPatIndices p)].

  However, in proofs, we often have to switch to this
  definition and forget that [lln] was [(bndngPatIndices p)].
  This is because when we induct on [lln],
  [nodeRenAlpha] might not be well typed anymore.
  Tail of [(bndngPatIndices p)] may not be
  [(bndngPatIndices p')] for any production [p'].
  
*)
Definition nodeRenAlphaAux 
   {G : CFGV} {vc : VarSym G}
   {mp : MixtureParam}
   (lln : list (list nat))
   (pts : Mixture mp)
   (lvAvoid : list (vType vc))
  : Mixture mp :=
let swPat :=  genPatSwapping pts lvAvoid in
let swTm := genTermSwapping lln swPat in
  mSwapTermPat pts swPat swTm.

Definition nodeRenAlpha 
   {G : CFGV} {vc : VarSym G}
   {p : TermProd G}
   (pts : Mixture (tpRhsAugIsPat p))
   (lvAvoid : list (vType vc))
  : Mixture (tpRhsAugIsPat p) :=
  nodeRenAlphaAux (bndngPatIndices p) pts lvAvoid.


(** swappings are determined at [tnode]
    the rest of these 3 mutual functions just
    keep recursing to cover all the (possibly embedded)
    sub[Term]s *)
Fixpoint tRenAlpha {G : CFGV} {vc : VarSym G}
  {gs : (GSym G)} (pt : Term gs) 
   (lvAvoid : list (vType vc))
   {struct pt} :  Term gs :=
match pt in Term gs return Term gs with
| tleaf a b => tleaf a b 
| vleaf vcc var => vleaf vcc var
| tnode p mix => tnode p 
      ( let mixR := mRenAlpha mix lvAvoid in
        nodeRenAlpha mixR lvAvoid)
end
with pRenAlpha {G : CFGV} {vc : VarSym G}
  {gs : (GSym G)} (pt : Pattern gs)
  (lvAvoid : list (vType vc)) {struct pt} : Pattern gs  :=
match pt with
| ptleaf a v => ptleaf a v
| pvleaf vcc var => pvleaf vcc var
| pnode p lpt => pnode p (mRenAlpha lpt lvAvoid)
| embed p nt => embed p (tRenAlpha nt lvAvoid)
end
with mRenAlpha {G : CFGV} {vc : VarSym G}
  {lgs : list (bool * GSym G)} (pts : Mixture lgs)
  (lvAvoid : list (vType vc))
 {struct pts}
      : Mixture lgs  := 
match pts in Mixture lgs return Mixture lgs with
| mnil  => mnil
| mtcons _ _ th ttl => 
        mtcons (tRenAlpha th lvAvoid)
               (mRenAlpha ttl lvAvoid)
| mpcons _ _ ph ptl =>
        mpcons  (pRenAlpha ph lvAvoid)
                (mRenAlpha ptl lvAvoid)
end.


(** one should be able to replace
  [bindersDeep] with [AllVars] thoughout in
  this statement/proof *)
Lemma swapCommonBinders : 
forall {G : CFGV} {vc : VarSym G},
(forall (s : GSym G) (ta : Term s) (sw: Swapping vc)
(lvA : list (vType vc)),
    subset (lvKeep lvA (tBndngVarsDeep vc ta)) (ALDom sw)
    -> disjoint (ALRange sw) (lvA++ (tAllVars ta))
    -> no_repeats (ALRange sw)
    -> disjoint (ALDom sw) (ALRange sw)
    -> disjoint (tBndngVarsDeep vc (tSwap ta sw)) lvA)
    *
(forall (s : GSym G) (pt : Pattern s) (sw: Swapping vc)
(lvA : list (vType vc)),
    subset (lvKeep lvA (pBndngVarsDeep vc pt)) (ALDom sw)
    -> disjoint (ALRange sw) (lvA++ (pAllVars pt))
    -> no_repeats (ALRange sw)
    -> disjoint (ALDom sw) (ALRange sw)
    -> disjoint (pBndngVarsDeep vc (pSwap pt sw)) lvA)
    *
(forall (l : MixtureParam) (ma: Mixture l) (sw: Swapping vc)
(lvA : list (vType vc)),
    subset (lvKeep lvA (mBndngVarsDeep vc ma)) (ALDom sw)
    -> disjoint (ALRange sw) (lvA++ (mAllVars ma))
    -> no_repeats (ALRange sw)
    -> disjoint (ALDom sw) (ALRange sw)
    -> disjoint (mBndngVarsDeep vc (mSwap ma sw)) lvA).
Proof.
  introv. GInduction; cpx; eauto with slow;[| |].
- Case "pvleaf". introv Hsub Hdis Hsdid Hnr.
  allsimpl. rewrite DeqSym. 
  rewrite DeqSym in Hdis.
  rewrite DeqSym in Hsub.
  ddeq; subst; allsimpl; cpx;[].
  repeat(disjoint_reasoning).
  duplicate Hdis.
  eapply swapVarInOrEq in Hdis;cpx.
  dorn Hdis.
  + disjoint_lin_contra.
  + duplicate X. rw Hdis in X.
    rw memberb_din in Hsub.
    revert Hsub. 
    cases_ifd Hs; introv Hsub;cpx.
    unfold subset in Hsub; allsimpl; dLin_hyp; try subst.
    eapply swapVarIn in Hdis1; cpx.
    disjoint_lin_contra.
- Case "mtcons".
  introns Hyp.
  allsimpl. repeat (disjoint_reasoning).
  allrw in_app_iff.
  dorn Hyp5.
  + eapply Hyp in Hyp5; eauto;
    repeat(disjoint_reasoning).
    unfold lvKeep in Hyp1.
    unfold lKeep in Hyp1.
    rw filter_app in Hyp1.
    rw subset_app in Hyp1. repnd.
    cpx.
  + eapply Hyp0 in Hyp5; eauto;
    repeat(disjoint_reasoning).
    unfold lvKeep in Hyp1.
    unfold lKeep in Hyp1.
    rw filter_app in Hyp1.
    rw subset_app in Hyp1. repnd. cpx.
- Case "mpcons".
  introns Hyp.
  allsimpl. repeat (disjoint_reasoning).
  allrw in_app_iff.
  dorn Hyp5.
  + eapply Hyp in Hyp5; eauto;
    repeat(disjoint_reasoning).
    unfold lvKeep in Hyp1.
    unfold lKeep in Hyp1.
    rw filter_app in Hyp1.
    rw subset_app in Hyp1. repnd.
    cpx.
  + eapply Hyp0 in Hyp5; eauto;
    repeat(disjoint_reasoning).
    unfold lvKeep in Hyp1.
    unfold lKeep in Hyp1.
    rw filter_app in Hyp1.
    rw subset_app in Hyp1. repnd. cpx.
Qed.

Definition AvRenaming {G : CFGV} {vc : VarSym G}
(lvA : list (vType vc)) (sw : Swapping vc)
:= no_repeats (ALRange sw)
    # disjoint (ALDom sw) (ALRange sw) 
    # disjoint (ALRange sw) lvA .

Lemma AvRenamingSubset : forall
   {G : CFGV} {vc : VarSym G}
(lvl lvr : list (vType vc)) 
(sw : Swapping vc),
subset lvr lvl
-> AvRenaming lvl sw
-> AvRenaming lvr sw.
Proof.
  unfold AvRenaming.
  introv Hs Hav. repnd.
  dands; cpx.
  SetReasoning.
Qed.


Lemma SwapTermPatSpec : 
  forall {G : CFGV} {vc : VarSym G},
  (forall (s : GSym G) (ta : Term s), True)
  *
  (forall (s : GSym G) (pt : Pattern s) 
  (swPat swTerm : Swapping vc)
  (lvA : list (vType vc)),
      subset (lvKeep lvA (pBndngVars vc pt)) (ALDom swPat)
      -> AvRenaming (lvA++ (pAllVars pt)) swPat
      -> AvRenaming (lvA++ (pAllVars pt)) swTerm
      -> disjoint (pAlreadyBndBinders vc pt) lvA
      -> disjoint lvA
                  (pBndngVarsDeep vc
                    (pSwapBindEmbed pt swPat swTerm)))
  *
  (forall (l : MixtureParam) (ma: Mixture l)
  (swPat swTerm : Swapping vc)
  (lvA : list (vType vc)),
  AvRenaming (lvA++ (mAllVars ma)) swTerm
  -> AvRenaming (lvA++ (mAllVars ma)) swPat
  -> disjoint (mAlreadyBndBinders vc ma) lvA
  -> subset (lvKeep lvA (mBndngVars vc ma)) (ALDom swPat)
  -> disjoint lvA (mBndngVarsDeep vc ( mSwapBindEmbed ma swPat swTerm))
               ).
Proof.
intros. GInduction; cpx;[| | |].
- Case "pvleaf".
  introv Hsub H1a H2a Hd.
  clear H2a. repnud H1a.
  allsimpl. rewrite DeqSym. 
  rewrite DeqSym in H1a.
  rewrite DeqSym in Hsub.
  ddeq; subst; allsimpl; cpx;[].
  repeat(disjoint_reasoning).
  duplicate H1a as Hdis.
  eapply swapVarInOrEq in Hdis;cpx.
  dorn Hdis;[|].
  + disjoint_lin_contra.
  + duplicate X. rw Hdis in X.
    rw memberb_din in Hsub.
    revert Hsub. 
    cases_ifd Hs; introv Hsub;cpx.
    unfold subset in Hsub; allsimpl; dLin_hyp; try subst.
    eapply swapVarIn in H1a; cpx.
    disjoint_lin_contra.
- Case "pembed". 
  introv ? ? Hpa Hta. clear Hpa.
  allsimpl. repnud Hta.
  repeat(disjoint_reasoning).
  apply disjoint_sym.
  apply swapCommonBinders; cpx;
  [|repeat(disjoint_reasoning)];[].
  unfold lvKeep.
  rewrite lKeepDisjoint; cpx.
  disjoint_reasoning.
- Case "mtcons".
  introv. intros ? ? ? ?.
  introv H1a H2a Hd.
  allsimpl.
  repeat (disjoint_reasoning).
  repnud H2a.
  repnud H1a.
  apply H0; cpx; unfold AvRenaming; repeat(disjoint_reasoning).
- Case "mpcons".
  introv. intros ? ? ? ?.
  introv H1a H2a Hd.
  allsimpl.
  repnud H2a.
  repnud H1a.
  repeat (disjoint_reasoning).
  + apply_hyp;
    cpx; unfold AvRenaming; dands;repeat(disjoint_reasoning);cpx.
    eapply subset_trans
    with (l2:=(lvKeep lvA (pBndngVars vc ph ++ mBndngVars vc ptl)));
     eauto.
    unfold lvKeep.
    apply monotoneFilter.
    eauto with SetReasoning.
  + apply_hyp;
    cpx; unfold AvRenaming; dands;repeat(disjoint_reasoning);cpx.
    eapply subset_trans
    with (l2:=(lvKeep lvA (pBndngVars vc ph ++ mBndngVars vc ptl)));
     eauto.
    unfold lvKeep.
    apply monotoneFilter.
    eauto with SetReasoning.
Qed.

  

Lemma ndRenAlAxSpecDisjAux : forall
   {G : CFGV} {vc : VarSym G}
   {mp : MixtureParam}
   (pts : Mixture mp)
  (lswPat lswTm : list (Swapping vc))
  (lvA : list (vType vc)),
  disjoint (mAlreadyBndBinders vc pts) lvA
  -> lForall (AvRenaming (lvA++ (mAllVars pts))) lswTm
  -> lForall (AvRenaming (lvA++ (mAllVars pts))) lswPat
  -> length lswTm = length mp
  -> liftRelPtwise (fun _ _ _ => True) 
          (fun s pt sw => 
              subset (lvKeep lvA (pBndngVars vc pt)) (ALDom sw))
              pts lswPat 
  -> disjoint (mAlreadyBndBinders vc pts) lvA
  -> disjoint (mBndngVarsDeep vc (mSwapTermPat pts lswPat lswTm)) 
             lvA.
Proof.
  induction pts; cpx.
- introv H1a H2a H3a H4a H5a H6a.
  allsimpl. destruct lswPat; cpx;[].
  repnd. GC.
  destruct lswTm as [|swh swt]; inverts H4a.
  repeat (disjoint_reasoning).
  + GC. repnud H2a. 
    repnud H2a0.
    apply swapCommonBinders; 
    repeat (disjoint_reasoning); cpx.
    unfold lvKeep.
    rewrite lKeepDisjoint; cpx;
    disjoint_reasoning.
  + allsimpl. exrepnd.
    apply IHpts; cpx.
    * apply lForallSame.
      apply lForallSame in H2a.
      apply implies_lforall with 
      (P:= (AvRenaming (lvA ++ tAllVars ph ++ mAllVars pts)));
      auto.
      introv xx. apply AvRenamingSubset; eauto.
      introv Hin.
      allrw in_app_iff.
      cpx.
    * apply lForallSame.
      apply lForallSame in H3a.
      apply implies_lforall with 
      (P:= (AvRenaming (lvA ++ tAllVars ph ++ mAllVars pts)));
      auto.
      introv xx. apply AvRenamingSubset; eauto.
      introv Hin.
      allrw in_app_iff.
      cpx.

- introv H1a H2a H3a H4a H5a H6a.
  allsimpl. destruct lswPat; cpx;[].
  repnd. GC.
  destruct lswTm as [|swh swt]; inverts H4a.
  allsimpl. repnd.
  repeat (disjoint_reasoning);[|].
  + GC. 
    repnud H2a0. simpl.
    repnud H3a0.
    apply disjoint_sym.
    allsimpl. repnd.
    apply (pcase SwapTermPatSpec); 
    repeat (disjoint_reasoning); cpx;
    unfold AvRenaming; cpx;dands;
    repeat (disjoint_reasoning);  cpx.
  + allsimpl. exrepnd.
     apply IHpts; cpx.
    * apply lForallSame.
      apply lForallSame in H2a.
      apply implies_lforall with 
      (P:= (AvRenaming (lvA ++ pAllVars ph ++ mAllVars pts)));
      auto.
      introv xx. apply AvRenamingSubset; eauto.
      introv Hin.
      allrw in_app_iff.
      cpx.
    * apply lForallSame.
      apply lForallSame in H3a.
      apply implies_lforall with 
      (P:= (AvRenaming (lvA ++ pAllVars ph ++ mAllVars pts)));
      auto.
      introv xx. apply AvRenamingSubset; eauto.
      introv Hin.
      allrw in_app_iff.
      cpx.

Qed.

Lemma genPatSwappingSpec6 : forall
   {G : CFGV} {vc : VarSym G}
  {lgs : list (bool * GSym G)} (pts : Mixture lgs)
   (lvAvoid : list (vType vc)),
  let lswap := genPatSwapping pts lvAvoid in
  length lswap = length lgs
  # lForall (AvRenaming (lvAvoid ++ mAllVars pts)) lswap.
Proof.
  intros.
  subst lswap.
  pose proof (genPatSwappingSpec pts lvAvoid) as XX.
  pose proof (genPatSwappingSpec3 pts lvAvoid) as YY.
  allsimpl.
  remember (genPatSwapping pts lvAvoid) as pss.
  repnd.
  dands;cpx.
  repeat (disjoint_reasoning).
  clear XX0 Heqpss.
  induction pss; cpx.
  allsimpl. unfold AvRenaming.
  rw no_repeats_app in XX1.
  repnd. dands;
  repeat (disjoint_reasoning); cpx.
Qed.

(** this is the heart of the proof
    of [RenAlphaAvoid].
    The main action happens in [nodeRenAlphaAux] at a [tnode].*)
Lemma ndRenAlAxSpecDisj : forall
   {G : CFGV} {vc : VarSym G}
   {mp : MixtureParam}
   (pts : Mixture mp)
   (lln : list (list nat))
   (lvAvoid : list (vType vc)),
  disjoint (mAlreadyBndBinders vc pts) lvAvoid
  -> disjoint (mBndngVarsDeep vc (nodeRenAlphaAux lln pts lvAvoid)) 
             lvAvoid.
Proof.
  introv Hdis.
  unfold nodeRenAlphaAux.
  remember (genPatSwapping pts lvAvoid) as ps.
  remember (genTermSwapping lln ps) as ts.
  pose proof (genPatSwappingSpec6 pts lvAvoid) as H6.
  allsimpl. exrepnd.
  apply ndRenAlAxSpecDisjAux; cpx.
  - admit.
  - subst ps; cpx.
  - admit.
  - apply genPatSwappingSpec5; cpx.
    subst ps; apply genPatSwappingSpec4; cpx.
Qed.


Lemma RenAlphaAvoid : forall {G : CFGV} {vc : VarSym G},
(  (forall (s : GSym G) (ta : Term s)
  (lvA : list (vType vc)),
      disjoint (tBndngVarsDeep vc (tRenAlpha ta lvA)) lvA)
   *
  (forall (s : GSym G) (pta : Pattern s)
  (lvA : list (vType vc)),
      disjoint (pAlreadyBndBinders vc (pRenAlpha pta lvA)) lvA)
   *
  (forall (l : MixtureParam) (ma: Mixture l) 
  (lvA : list (vType vc)),
      disjoint (mAlreadyBndBinders vc (mRenAlpha ma lvA)) lvA)).
Proof.
intros. GInduction; intros; cpx; 
  try (allsimpl; repeat (disjoint_reasoning); cpx; fail);[].
  Case "tnode".
  allsimpl. unfold nodeRenAlpha.
  specialize (H lvA).
  remember (mRenAlpha m lvA) as pts.
  apply ndRenAlAxSpecDisj; auto.
Qed.


Theorem lbShallowNoChange: forall 
  {G : CFGV} {vc : VarSym G},
(   forall (s : GSym G) (nt : Term s), True)
*
(   forall (s : GSym G) (pt : Pattern s) 
    (lvA : list (vType vc)),
    pBndngVars vc pt = pBndngVars  vc (pRenAlpha pt lvA)
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l) 
    (lvA : list (vType vc))
    (nn : nat),
    getBVarsNth vc m nn = @getBVarsNth 
                            _ vc _ (mRenAlpha m lvA) nn
).
 intros. 
  GInduction; allsimpl; introns Hyp; intros; cpx;[ | | ].
  - Case "pnode". simpl. simpl pBndngVars. 
    rewrite mBndngVarsAsNth.
    rewrite mBndngVarsAsNth.
    autorewrite with fast.
    apply eq_flat_maps.
    intros nn Hin. cpx.
  - simpl. destruct nn; cpx.
  - simpl. destruct nn; cpx.
Qed.

Lemma  mRenlBinderShallowSame : forall
  {G : CFGV} {vc : VarSym G}
 (l : MixtureParam) (m : Mixture l)
 (lvA : list (vType vc))
  (la : list (list nat)),
lBoundVars vc la m =  lBoundVars vc la (mRenAlpha m lvA).
Proof.
  intros. unfold lBoundVars.
  apply eq_maps.
  intros n Hin.
  apply eq_flat_maps.
  intros nn Hinn.
  clear dependent n.
  clear dependent la.
  apply (mcase lbShallowNoChange).
Qed.

Lemma xxx: forall
   {G : CFGV} {vc : VarSym G}
   (lswP : list (Swapping vc))
   {mp : MixtureParam}
   (m : Mixture mp)
   (lln : list (list nat)),
lBoundVars vc lln (mSwapTermPat m lswP (genTermSwapping lln lswP))
  = map (fun p => swapLVar (snd p) (fst p) )
    (combine (lBoundVars vc lln m) (genTermSwapping lln lswP)).
Proof.
  intros.
  apply eq_maps2 with (defa:=[]) (defc:=([],[]));
  [unfold genTermSwapping, lBoundVars;
    rw combine_length;
    autorewrite with fast;rw  min_eq; sp |].
  introv Hlt.
  destruct lln; cpx.
  allsimpl.






  

Lemma ndRenAlAxAlpha3 : forall
   {G : CFGV} {vc : VarSym G}
   (lswP : list (Swapping vc))
   (n:nat)
   {mp : MixtureParam}
   (m : Mixture mp)
   (lln : list (list nat)),
n< length mp ->
let labs := (MakeAbstractionsTNodeAux vc lln m) in
let labsR := (MakeAbstractionsTNodeAux vc
                lln
                (mSwapTermPat m lswP (genTermSwapping lln lswP))) in
match (nth_error labs n, nth_error labsR n) with
| (Some ab, Some abR) 
    => AlphaEqAbs ab abR
| _ => False  
end.
Proof.
induction n.
- introv Hn. destruct m; cpx.
  unfold MakeAbstractionsTNodeAux.
  allsimpl.
  remember (genTermSwapping lln lswP) as swT.
  remember (mSwapTermPat (mtcons ph m) lswP swT) as RR.
  duplicate HeqRR.
  simpl in HeqRR.
  rw HeqRR0 in HeqRR.
  rewrite <- HeqRR.
  allsimpl.
Abort.

 

Lemma ndRenAlAxAlpha2 : forall
   {G : CFGV} {vc : VarSym G}
   (lswP : list (Swapping vc))
   {mp : MixtureParam}
   (m : Mixture mp)
   (lln : list (list nat)),
mAlphaEq vc  m
          (mSwapTermPat m lswP (genTermSwapping lln lswP))
          lln.
Proof.
  unfold mAlphaEq. induction m; cpx.
  unfold MakeAbstractionsTNodeAux.
- intros. allsimpl.
  constructor.
  + destruct lln as [|lnh lnt];
    [allsimpl; autorewrite with fast;
      apply AlphaEqNilAbsT; eauto with Alpha; fail|].
    induction lnh as [|n ntl]; allsimpl; cpx;
     autorewrite with fast;
    [apply AlphaEqNilAbsT; eauto with Alpha; fail|].
    destruct a; cpx.

    
    
  
  
    


Admitted.

(** this is the heart of the proof
    of [RenAlphaAlpha].
    The main action happens in [nodeRenAlphaAux] at a [tnode].*)
Lemma ndRenAlAxAlpha : forall
   {G : CFGV} {vc : VarSym G}
   {mp : MixtureParam}
   (m : Mixture mp)
   (lln : list (list nat))
   (lvA : list (vType vc)),
lAlphaEqAbs (MakeAbstractionsTNodeAux vc lln m)
  (MakeAbstractionsTNodeAux vc lln (nodeRenAlphaAux lln m lvA)).
Proof.
  unfold MakeAbstractionsTNodeAux.
  induction m; cpx.
- introv. allsimpl. constructor.
  + induction lln; allsimpl; cpx; autorewrite with fast;
    [apply AlphaEqNilAbsT; cpx|].

    


Admitted.


Lemma RenAlphaAlpha : forall {G : CFGV} {vc : VarSym G},
(  (forall (s : GSym G) (ta : Term s)
  (lvA : list (vType vc)),
      tAlphaEq vc ta (tRenAlpha ta lvA))
   *
  (forall (s : GSym G) (pta : Pattern s)
  (lvA : list (vType vc)),
      pAlphaEq vc pta (pRenAlpha pta lvA))
   *
  (forall (l : MixtureParam) (ma: Mixture l)
  (llbv : list (list (vType vc)))
  (lvA : list (vType vc)),
  let maR := mRenAlpha ma lvA in
    lAlphaEqAbs (MakeAbstractions vc ma llbv) 
                (MakeAbstractions vc maR llbv))).
Proof.
intros. GInduction; intros; cpx; 
  try (econstructor; eauto; fail);[| |].

- Case "tnode".
  allsimpl.
  constructor.
  unfold MakeAbstractionsTNode.
  unfold nodeRenAlpha.
  
  eapply (alphaEqTransitive);
  [ |apply ndRenAlAxAlpha with (lvA0 := lvA); eauto].
  unfold MakeAbstractionsTNodeAux.
  rw <- (@mRenlBinderShallowSame G vc).
  apply X; cpx.

- Case "mtcons".
  subst maR.
  allunfold MakeAbstractionsTNodeAux.
  simpl. constructor; cpx.
  apply AlphaEqNilAbsT; cpx.

- Case "mpcons".
  subst maR.
  allunfold MakeAbstractionsTNodeAux.
  simpl. constructor; cpx.
  apply AlphaEqNilAbsP; cpx.

Qed.



