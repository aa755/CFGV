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
Require Export AlphaEqProps.
Set Implicit Arguments.

(* [lVars] is explicitly a function on [vc].
    the typechecker will then happily export
    the transport in the [pvleaf] clause of [pRenBinders]. *)
Definition lVars {G : CFGV} 
  ( vc  : VarSym G) := list (vType vc).
  
(** renames all binding variables
    to distinct ones that are not 
    in [lvAvoid] *)
Fixpoint pRenBinders {G : CFGV} 
  { vc  : VarSym G}
  {gs : (GSym G)} 
  (lvAvoid : lVars vc)
  (p : Pattern gs)
   {struct p} : Pattern gs  :=
match p in Pattern gs return Pattern gs with
| ptleaf tc t =>  ptleaf tc t
| pvleaf vcc var => pvleaf vcc
                    (match (DeqVarSym vc vcc) with
                    | left eqq => (vFreshVar (transport eqq lvAvoid) var)
                    | right _ => var
                    end) 
| pnode p mix => pnode p (mRenBinders lvAvoid mix)
| embed p t => embed p t
end
with mRenBinders {G : CFGV} 
  { vc  : VarSym G}
  {lgs : list (bool * GSym G)} 
  (lvAvoid : list (vType vc))
   (pts : Mixture lgs)
   {struct pts} : Mixture lgs  := 
match pts with
| mnil => mnil
| mtcons _ _ ph ptl =>  mtcons ph (mRenBinders lvAvoid ptl)
| mpcons _ _ ph ptl => let phr := (pRenBinders lvAvoid ph) in
                       let phrb := pBndngVars vc phr in
                       mpcons phr  
                              (mRenBinders (lvAvoid ++ phrb) ptl)
end.


Lemma RenBindersSpec : forall {G : CFGV} (vc  : VarSym G), 
(   forall (s : GSym G) (nt : Term s), True)
*
(   forall (s : GSym G) (pt : Pattern s)  (lvAvoid : lVars vc),
    let ptr := (pRenBinders lvAvoid pt) in
    no_repeats (pBndngVars vc ptr)
    # disjoint (pBndngVars vc ptr) lvAvoid
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l)
    (lvAvoid : lVars vc),
    let mr := (mRenBinders lvAvoid m) in
    no_repeats (mBndngVars vc mr)
    # disjoint (mBndngVars vc mr) lvAvoid
).
Proof. 
 intros. GInduction; cpx;[|].
- Case "pvleaf".  allsimpl. intros.
  dands; rewrite DeqSym; ddeq; subst; 
  allsimpl; try constructor; cpx.
  repeat (disjoint_reasoning).
  apply vFreshVarSpec.

- Case "mpcons".
  introns Hyp.
  allsimpl. intros.
  specialize (Hyp0 (lvAvoid ++ (pBndngVars vc (pRenBinders lvAvoid ph)))).
  specialize (Hyp lvAvoid ).
  allrw no_repeats_app.
  repnd; dands;cpx; repeat (disjoint_reasoning); cpx.
Qed.


Lemma RenBindersSpec2 : forall {G : CFGV} (vc  : VarSym G),  
(   forall (s : GSym G) (nt : Term s), True)
*
(   forall (s : GSym G) (pt : Pattern s)  (lvAvoid : lVars vc),
    pAlreadyBndBinders vc pt
      = pAlreadyBndBinders vc (pRenBinders lvAvoid pt)
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l)
    (lvAvoid : lVars vc),
    mAlreadyBndBinders vc m
      = mAlreadyBndBinders vc (mRenBinders lvAvoid m)
).
Proof.
  intros; GInduction; allsimpl; cpx;[|]; intros; f_equal; cpx.
Qed.

Lemma RenBindersSpec3 : forall {G : CFGV} (vc  : VarSym G),  
(   forall (s : GSym G) (nt : Term s), True)
*
(   forall (s : GSym G) (pt : Pattern s)  (lvAvoid : lVars vc),
    pAllButBinders vc pt
      = pAllButBinders vc (pRenBinders lvAvoid pt)
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l)
    (lvAvoid : lVars vc),
    mAllButBinders vc m
      = mAllButBinders vc (mRenBinders lvAvoid m)
).
Proof.
  intros; GInduction; allsimpl; cpx;
      [|]; intros; f_equal; cpx.
Qed.

(*
Fixpoint mSwapTermEmbed
       {G  : CFGV}
       {vc : VarSym G}
       {lgs : list (bool * GSym G)}
       (pts : Mixture lgs)
       (sw : list (Swapping vc))
       {struct pts}
     : Mixture lgs  :=
match pts with
| mnil => mnil
| mtcons _ _ th ttl => 
    mtcons (tSwap th (lhead sw))
           (mSwapTermEmbed ttl (tail sw))
| mpcons _ _ ph ptl => 
    mpcons (pSwapEmbed ph  (lhead sw))
           (mSwapTermEmbed ptl  (tail sw))
end.
*)

Fixpoint mLSwapTermEmbed
       {G  : CFGV}
       {vc : VarSym G}
       {lgs : list (bool * GSym G)}
       (pts : Mixture lgs)
       (llbvOld llbvNew : list (lVars vc))
       {struct pts}
     : Mixture lgs  :=
match pts with
| mnil => mnil
| mtcons _ _ th ttl => 
    mtcons (tSwap th (combine (lhead llbvOld) (lhead llbvNew)))
           (mLSwapTermEmbed ttl (tail llbvOld) (tail llbvNew))
| mpcons _ _ ph ptl => 
    mpcons (pSwapEmbed ph (combine (lhead llbvOld) (lhead llbvNew)))
           (mLSwapTermEmbed ptl (tail llbvOld) (tail llbvNew))
end.

Definition nodeRenAlphaAux 
   {G : CFGV} {vc : VarSym G}
   {mp : MixtureParam}
   (lln : list (list nat))
   (rmix : Mixture mp)
   (lvAvoid : list (vType vc))
  : Mixture mp :=

  if (decDisjointV vc (mBndngVars vc rmix) lvAvoid)
  then
    rmix
  else
    let llbvOld := lBoundVars vc lln rmix in
    let rmixPR := mRenBinders (lvAvoid ++ (mAllVars rmix)) rmix in
    let llbvNew := lBoundVars vc lln rmixPR in
    mLSwapTermEmbed rmixPR llbvOld llbvNew.


Fixpoint tRenAlpha {G : CFGV} {vc : VarSym G}
  {gs : (GSym G)} (pt : Term gs) 
   (lvAvoid : list (vType vc))
   {struct pt} :  Term gs :=
match pt in Term gs return Term gs with
| tleaf a b => tleaf a b 
| vleaf vcc var => vleaf vcc var
| tnode p mix => tnode p 
      ( let rmix := mRenAlpha mix lvAvoid in
        nodeRenAlphaAux (bndngPatIndices p) rmix lvAvoid
        )
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



Lemma ndRenAlAxSpecDisjAux : forall
   {G : CFGV} {vc : VarSym G}
   {mp : MixtureParam}
   (pts : Mixture mp)
  (llbvOld llbvNew : list (lVars vc))
  (lvA : list (vType vc)),
  disjoint (mAlreadyBndBinders vc pts) lvA
  -> lForall no_repeats llbvNew
  -> disjoint (flatten llbvNew) (lvA ++ 
          mAllButBinders vc pts ++ flatten llbvOld)
  -> map (@length _) llbvOld =  map (@length _) llbvNew
  -> length llbvOld = length mp
  -> disjoint (mAlreadyBndBinders vc pts ++ mBndngVars vc pts) lvA
  -> disjoint (mBndngVarsDeep vc (mLSwapTermEmbed pts llbvOld llbvNew)) 
             lvA.
Proof.
  induction pts; cpx;[|].
- introv H1a H2a H3a H4a H5a H6a.
  applydup map_eq_length_eq in H4a.
  allsimpl. dlist_len llbvOld. allsimpl.
  dlist_len llbvNew. allsimpl.
  inverts H4a.
  allrw no_repeats_app.
  repeat (disjoint_reasoning).
  + GC. 
    apply tSwapBndngVarsDisjoint; cpx;
    repeat(disjoint_reasoning).
  + allsimpl. exrepnd.
    apply IHpts; cpx; repeat(disjoint_reasoning).

- introv H1a H2a H3a H4a H5a H6a.
  applydup map_eq_length_eq in H4a.
  allsimpl. dlist_len llbvOld. allsimpl.
  dlist_len llbvNew. allsimpl.
  inverts H4a.
  allrw no_repeats_app.
  repeat (disjoint_reasoning).
  + GC. apply disjoint_sym.
    apply (pcase SwapEmbedSpec); cpx;
    autorewrite with fast; try congruence;
     cpx;  repeat (disjoint_reasoning).
  + allsimpl. exrepnd.
    apply IHpts; cpx; repeat(disjoint_reasoning).
Qed.


Lemma mRenBindersSpec3 : forall
  {G : CFGV} {vc  : VarSym G}
   {mp : MixtureParam}
   (pts : Mixture mp)
   (lln : list (list nat))
   (lvAvoid : list (vType vc)),
   validBsl (length mp) lln 
  -> 
lForall no_repeats
  (lBoundVars vc lln (mRenBinders (lvAvoid) pts)).
Proof.
  intros.
  pose proof  ((mcase (RenBindersSpec vc)) _ pts lvAvoid)  as Hs.
  simpl in Hs.
  repnd. 
  rewrite mBndngVarsAsNth in Hs0. clear Hs. 
  rw (@lForallSame (list (vType vc))).
  unfold lBoundVars.
  introv Hin.
  apply in_map_iff in Hin.
  exrepnd. subst. rename a0 into ln.
  apply X in Hin1.
  repnud Hin1.
  induction ln; cpx.
  allrw no_repeats_cons.
  allsimpl. repnd.
  apply IHln in Hin2; cpx;[].
  clear IHln.
  allrw no_repeats_app.
  dands;cpx.
  - apply  no_rep_flat_map_seq1 with (n:=0) (len := length mp); sp.
    apply LInSeqIff; dands; omega.
  - intros. introv Hin Hinc.
    apply lin_flat_map in Hinc.
    exrepnd.
    destruct (deq_nat x a); subst; cpx.
    (* for diff indices, they are disjoint *)
    eapply no_rep_flat_map_seq2 in n; eauto.
    + disjoint_lin_contra.
    + rw (@lForallSame nat) in Hin1.
      apply Hin1 in Hinc1.
      apply LInSeqIff; dands; omega.
    + apply LInSeqIff; dands; omega.
Qed.

Theorem renBindersSameLength: forall
{G : CFGV} {vc : VarSym G},
(   forall (s : GSym G) (nt : Term s), True)
*
(   forall (s : GSym G) (pt : Pattern s) (lvA : lVars vc),
    length (pBndngVars vc pt) 
      = length (pBndngVars  vc (pRenBinders lvA pt))
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l) 
    (lvA : lVars vc)
    (nn : nat),
    length (getBVarsNth vc m nn) = 
        length (getBVarsNth vc (mRenBinders lvA m) nn)
).
Proof.
  intros.
 GInduction; allsimpl; introns Hyp; intros; cpx;
[ | | | ].
  - Case "pvleaf". rewrite DeqSym.
    symmetry. rewrite DeqSym.
    ddeq; subst; sp.

  - Case "pnode".
    simpl. simpl pBndngVars.
    rewrite mBndngVarsAsNth.
    rewrite mBndngVarsAsNth.
    rewrite len_flat_map.
    rewrite len_flat_map.
    f_equal.
    apply eq_maps.
    cpx.
  - simpl. destruct nn; cpx.
  - simpl. destruct nn; cpx.
Qed.

Lemma renBindersLBVLenSame :
forall {G : CFGV} {vc : VarSym G}
(l : list (bool # GSym G)) (pts : Mixture l) 
    (lvA : lVars vc)
    (lln : list (list nat)),
map (@length _) (lBoundVars vc lln pts) =
map (@length _) (lBoundVars vc lln (mRenBinders lvA pts)).
Proof.
  intros.
  apply lBoundVarsLenSameifNth.
  pose proof (@renBindersSameLength G vc).
  dands; cpx.
Qed.

Hint Resolve (fun G vc => mcase (@ bindersAllvarsSubset G vc)) 
 lBoundVarsmBndngVars :
  SetReasoning.






Lemma ndRenAlAxSpecDisj : forall 
  {G : CFGV} {vc  : VarSym G}
   {mp : MixtureParam}
   (pts : Mixture mp)
   (lln : list (list nat))
   (lvAvoid : list (vType vc)),
   validBsl (length mp) lln 
  -> length lln = length mp
  -> disjoint (mAlreadyBndBinders vc pts) lvAvoid
  -> disjoint (mBndngVarsDeep vc (nodeRenAlphaAux lln pts lvAvoid)) 
             lvAvoid.
Proof.
  introv Hnr Hlen Hdis.
  unfold nodeRenAlphaAux.
  cases_ifd Hdddd; cpx;
    [ apply disjointDeepShallowPlusAlready; 
      repeat (disjoint_reasoning) |].
  pose proof ((mcase (RenBindersSpec vc)) _ pts (lvAvoid ++ mAllVars pts))  as Hs.
  simpl in Hs. exrepnd.
  apply ndRenAlAxSpecDisjAux; 
  try rewrite <- (mcase (RenBindersSpec2 vc));
  try rewrite <- (mcase (RenBindersSpec3 vc)); cpx.
  - apply mRenBindersSpec3; cpx.
  - eapply subset_disjointLR; eauto.
    + apply lBoundVarsmBndngVars.
    + apply subset_app_lr; eauto;[].
      apply subset_app. dands;
      eauto 2 with SetReasoning.
  - apply renBindersLBVLenSame.
  - unfold lBoundVars.
    autorewrite with fast. trivial.
  - repeat (disjoint_reasoning).
Qed.





Lemma RenAlphaAvoid : forall {G : CFGV} {vc  : VarSym G},
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
  allsimpl. 
  specialize (H lvA).
  remember (mRenAlpha m lvA) as pts.
  apply ndRenAlAxSpecDisj; auto.
  - rewrite length_pRhsAugIsPat.
    apply bndngPatIndicesValid2; auto.
    
  - unfold bndngPatIndices.
    unfold tpRhsAugIsPat. unfold prhsIsBound.
    rw combine_length.
    unfold tpRhsSym. simpl.
    autorewrite with fast.
    rw min_eq; auto.
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
  intros. apply lBoundVarsSameifNth.
  apply (mcase lbShallowNoChange).
Qed.

Lemma  mBndngVarsShallowSame : forall
  {G : CFGV} {vc : VarSym G}
 (l : MixtureParam) (m : Mixture l)
 (lvA : list (vType vc)),
  mBndngVars vc m =  mBndngVars vc (mRenAlpha m lvA).
Proof.
  intros. apply mBndngVarsSameIfNth.
  apply (mcase lbShallowNoChange).
Qed.


Lemma mLSwapTermEmbedSameBinders : forall
   {G : CFGV} {vc : VarSym G}
   {mp : MixtureParam}
   (m : Mixture mp)
   (lla llb : list (list (vType vc))),
(mBndngVars vc (mLSwapTermEmbed m lla llb))
  = mBndngVars vc m.
Proof.
  induction m; cpx;[].
  simpl. intros.
  f_equal; cpx;[].
  symmetry.
  apply (pcase SwapEmbedSameBinders).
Qed.

Lemma mLSwapTermEmbedSameNthBinder : forall
   {G : CFGV} {vc : VarSym G}
   {mp : MixtureParam}
   (m : Mixture mp)
   (lla llb : list (list (vType vc)))
   (nn : nat),
    getBVarsNth vc m nn = getBVarsNth 
                             vc (mLSwapTermEmbed m lla llb) nn.
Proof.
  induction m; cpx; intros ; destruct nn; allsimpl; cpx.
  apply (pcase SwapEmbedSameBinders).
Qed.


Lemma pRenBindersAlpha : forall {G : CFGV} {vc : VarSym G},
(  (forall (s : GSym G) (ta : Term s), True)
   *
  (forall (s : GSym G) (pta : Pattern s)
  (lvA : list (vType vc)),
      pAlphaEq vc pta (pRenBinders lvA pta))
   *
  (forall (mp : MixtureParam) (ma: Mixture mp)
  (llbv : list (list (vType vc)))
  (lvA : list (vType vc)),
  (forall b s, LIn (b,s) mp -> b= true)
  -> let maR := mRenBinders lvA ma in
    lAlphaEqAbs (MakeAbstractions vc ma llbv) 
                (MakeAbstractions vc maR llbv))).
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
Qed.


Lemma mLSwapTermEmbedSameLBV : forall
   {G : CFGV} {vc : VarSym G}
   {mp : MixtureParam}
   (m : Mixture mp)
   (lla llb : list (list (vType vc)))
   (lln : list (list nat)),
    lBoundVars vc lln m = lBoundVars
                             vc  lln (mLSwapTermEmbed m lla llb).
Proof.
  intros.
  apply lBoundVarsSameifNth.
  apply mLSwapTermEmbedSameNthBinder.
Qed.
  

Definition swapEmbedAbs {G : CFGV} {vc : VarSym G}
           (a : Abstraction G vc)
           (sw : Swapping vc)
    : (Abstraction G vc):=
match a with
| termAbs _ lbv t =>  termAbs _ lbv t
| patAbs _ lbv t => patAbs _ lbv (pSwapEmbed t sw)
end.

Definition swapEmbedLAbs {G : CFGV} {vc : VarSym G}
           (la : list (Abstraction G vc))
           (sw : Swapping vc)
    : list (Abstraction G vc):=
map (fun x => swapEmbedAbs x sw) la.

Lemma MakeLAbsSwapCommute:
forall {G : CFGV} {vc : VarSym G} (mp : MixtureParam) 
  (sw : Swapping vc) (m : Mixture mp)
  (lbv : list (lVars vc)),
swapEmbedLAbs (MakeAbstractions vc m lbv) sw =
MakeAbstractions vc (mSwapEmbed m sw) lbv.
Proof.
  unfold swapEmbedLAbs.
  intros G vc np sw m.
  induction m;  intros; allsimpl; cpx; f_equal; cpx;
   destruct lbv; allsimpl; cpx.
Qed.



Lemma ndRenAlAxAlpha : forall
   {G : CFGV} {vc : VarSym G}
   {mp : MixtureParam}
   (m : Mixture mp)
   (lln : list (list nat))
   (lvA : list (vType vc)),
   validBsl (length mp) lln 
  -> 
lAlphaEqAbs (MakeAbstractionsTNodeAux vc lln m)
  (MakeAbstractionsTNodeAux vc lln (nodeRenAlphaAux lln m lvA)).
Proof.
  unfold MakeAbstractionsTNodeAux.
  introv Hv.
  unfold nodeRenAlphaAux.
  cases_ifd Hdddd; cpx; eauto with Alpha;[]; clear Hddddf.
  rewrite <- mLSwapTermEmbedSameLBV.
  pose proof (renBindersLBVLenSame m (lvA ++ mAllVars m) lln) as Hlen.
  pose proof (@mRenBindersSpec3 G vc 
      mp m lln (lvA ++ mAllVars m)) as Hnr.
  apply Hnr in Hv.
  clear Hnr.
  pose proof 
    ((mcase (RenBindersSpec vc)) _ 
      m (lvA ++ mAllVars m))  as Hd.
  simpl in Hd.
  repnd. clear Hd0.
  assert (
      disjoint 
        (flatten (lBoundVars vc lln 
          (mRenBinders (lvA ++ mAllVars m) m)))
       (lvA ++ (flatten (lBoundVars vc lln m)))
    ) as Hld by
    (apply (subset_disjointLR Hd); auto;
    [ eauto with SetReasoning |
    apply subset_app_lr; eauto 2 with SetReasoning]).
    
  assert (
      disjoint 
        (flatten (lBoundVars vc lln 
          (mRenBinders (lvA ++ mAllVars m) m)))
       (lvA ++ (mAllVars m))
    ) as Had by
    (apply (subset_disjointLR Hd); eauto with SetReasoning).

    clear Hd.
  repeat disjoint_reasoning.
  clear Had0 Hld0.
  remember (lBoundVars vc lln m) as lbva.
  remember (lBoundVars vc lln 
    (mRenBinders (lvA ++ mAllVars m) m)) as lbvb.
  applydup map_eq_length_eq in Hlen.
  clear Heqlbvb.
  clear Heqlbva.
  remember (lvA ++ mAllVars m) as lv.
  clear Heqlv.
  revert lv.
  generalize dependent lbvb.
  generalize dependent lbva.
  clear lln lvA.
  induction m as [ | ? ? ph ptl Hind| ? ? ph ptl Hind]; cpx.
- allsimpl. intros. constructor; cpx.
  + destruct lbva as [|la lvba]; allsimpl; 
    destruct lbvb as [|lb lbvv];
    inverts Hlen0;
    autorewrite with fast; simpl;
    [apply AlphaEqNilAbsT; eauto with Alpha; fail|].
    pose proof (GFreshDistRenWSpec vc la
                (tAllVars ph++
                (tAllVars (tSwap ph (combine la lb)))
                    ++ la ++lb)) as Hfr.
    exrepnd.
    allsimpl. inverts Hlen.
    apply alAbT with (lbnew:=lvn); try congruence;
    repeat (disjoint_reasoning);
    [unfolds_base; simpl; dands; cpx;
    autorewrite with fast;
    repeat(disjoint_reasoning); fail |].

    rewrite (tcase swap_app).
    autorewrite with slow; try congruence;
    cpx; repeat (disjoint_reasoning);
    eauto with Alpha.

  + apply Hind; destruct lbva; destruct lbvb;
    allsimpl; repeat (disjoint_reasoning);
    inverts Hlen0; inverts Hlen; cpx.

- allsimpl. intros. constructor; cpx.
  + eapply alphaEqTransitive.
    instantiate (1 :=
    (patAbs vc (lhead lbvb)
       (pSwap ph
        (combine (lhead lbva) (lhead lbvb))))
   ).


   *  destruct lbva as [|la lvba]; allsimpl; 
      destruct lbvb as [|lb lbvv];
      inverts Hlen0;
      autorewrite with fast; simpl;
      [apply AlphaEqNilAbsP; eauto with Alpha; fail|].
      pose proof (GFreshDistRenWSpec vc la
                  (pAllVars ph++
                  (pAllVars (pSwap ph (combine la lb)))
                      ++ la ++lb)) as Hfr.
      exrepnd.
      allsimpl. inverts Hlen.
      apply alAbP with (lbnew:=lvn); try congruence;
      repeat (disjoint_reasoning);
      [unfolds_base; simpl; dands; cpx;
      autorewrite with fast;
      repeat(disjoint_reasoning) |].
   
      rewrite (pcase swap_app).
      autorewrite with slow; try congruence;
      cpx; repeat (disjoint_reasoning);
      eauto with Alpha.

   * apply AlphaEqNilAbsP.
     apply alphaEqSym.
  eapply alphaEqTransitive.
    instantiate (1 :=
        (pSwap (pRenBinders lv ph) 
            (combine (lhead lbva) (lhead lbvb))) 
   ).
     apply  (pcase (@pAlphaSwapEmSwap G vc)).
     apply alphaEqSym.
     apply alphaEquiVariant.
     apply pRenBindersAlpha.
  + apply Hind; destruct lbva; destruct lbvb;
    allsimpl; repeat (disjoint_reasoning);
    inverts Hlen0; inverts Hlen; cpx.
Qed.




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
  unfold nodeRenAlphaAux.
  
  eapply (alphaEqTransitive);
  [ |apply ndRenAlAxAlpha with (lvA0 := lvA); eauto].
  unfold MakeAbstractionsTNodeAux.
  rw <- (@mRenlBinderShallowSame G vc).
  apply X; cpx.
  unfold tpRhsAugIsPat. unfold prhsIsBound.
  rw combine_length.
  unfold tpRhsSym.
  autorewrite with fast.
  rw min_eq; auto.
  apply bndngPatIndicesValid2; auto.
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

Ltac addRenSpec :=
match goal with
[ |- context [@tRenAlpha ?G ?vc ?gs ?a ?lv] ]
  =>  let Hala := fresh "Hal" a in 
      let Hdis := fresh "Hdis" a in 
      pose proof ((tcase (@RenAlphaAlpha G vc))
              gs a lv) as Hala;
      pose proof ((tcase (@RenAlphaAvoid G vc))
              gs a lv) as Hdisa
end.

Lemma RenAlphaNoChange : forall {G : CFGV} {vc : VarSym G},
(  (forall (s : GSym G) (ta : Term s)
  (lvA : list (vType vc)),
    disjoint (tBndngVarsDeep vc ta) lvA 
      -> ta = (tRenAlpha ta lvA))
   *
  (forall (s : GSym G) (pta : Pattern s)
  (lvA : list (vType vc)),
    disjoint (pBndngVarsDeep vc pta) lvA 
      -> pta = (pRenAlpha pta lvA))
   *
  (forall (l : MixtureParam) (ma: Mixture l)
  (lvA : list (vType vc)),
    disjoint (mBndngVarsDeep vc ma) lvA 
    -> ma = mRenAlpha ma lvA)).
Proof.
  intros.
  GInduction; introns Hyp; allsimpl; 
  try (f_equal; cpx; fail);[ | | ].

- Case "tnode". f_equal.
  unfolds_base.
  cases_ifd Hdd; cpx.
  rewrite <- mBndngVarsShallowSame in Hddf.
  provefalse. apply Hddf.
  SetReasoning.

- Case "mtcons". allsimpl. repeat (disjoint_reasoning).
  f_equal; cpx.

- Case "mpcons". allsimpl. repeat (disjoint_reasoning).
  f_equal; cpx.
Qed.

Lemma tRenWithSpec :
  forall  {G : CFGV} {vc : VarSym G}
     (s : GSym G) (ta : Term s)
     (lvA : list (vType vc)),
  {tar : Term s $ tAlphaEq vc ta tar #
          disjoint (tBndngVarsDeep vc tar) lvA}.
Proof.
  intros.
  exists (tRenAlpha ta lvA).
  pose proof (@RenAlphaAlpha G vc).
  pose proof (@RenAlphaAvoid G vc).
  repnd.
  dands; cpx.
Qed.

(* only comments below *)

(*
Lemma AllVarsEquivariant :
  forall {G : CFGV} {vc : VarSym G}
  (sw : Swapping vc),
    (forall (gs : GSym G) (t : Term gs), True)
    *
    (forall (gs : GSym G),
    EquiVariantFn (@pSwap _ vc gs)
                  (@pSwap _ vc gs)
                  (fun t => pSwapEmbed t sw))
    *
    (forall (lgs : list (bool * GSym G)),
     EquiVariantFn (@mSwap _ vc lgs)
                (@mSwap _ vc lgs)
                (fun t => mSwapEmbed t sw)).
Proof.
  intros.
  GInduction; auto; introns Hyp; intros; allsimpl ; auto.

- Case "pembed". f_equal.
  
simpl. rewrite DeqSym. symmetry. rewrite DeqSym.
  destruct_head_match; try subst;  cpx.

- simpl. rewrite DeqSym. symmetry. rewrite DeqSym.
  destruct_head_match; try subst;  cpx.

- unfold swapLVar. rw map_app.
  unfold swapLVar in Hyp0. 
  unfold swapLVar in Hyp. 
  f_equal; cpx.

- unfold swapLVar. rw map_app.
  unfold swapLVar in Hyp0. 
  unfold swapLVar in Hyp. 
  f_equal; cpx.
Qed.
*)

(*
Lemma swapDisjChain : forall  {G : CFGV} {vc : VarSym G}
  (vsa vs vsb : lVars vc),
    length vs = length vsa
    -> length vs = length vsb
    -> no_repeats vs
    -> no_repeats vsb
    -> 
  ((forall (gs : GSym G) (t : Term gs), True)
  *
  (forall (gs : GSym G) (t : Pattern gs),
       disjoint vs (vsa ++ vsb ++ (pAllVars t))
       -> disjoint vsb (vsa ++ pAllVars t)
       -> (pSwap (pSwapEmbed t (combine vsa vs)) (combine vs vsb))
            = pSwap t (combine vsa vsb))

    *
  (forall (lgs : MixtureParam) (m : Mixture lgs) ,
       disjoint vs (vsa ++ vsb ++ (mAllVars m))
       -> disjoint vsb (vsa ++ mAllVars m)
       -> (mSwap (mSwapEmbed m (combine vsa vs)) (combine vs vsb))
            = mSwap m (combine vsa vsb))).
Proof.
  introv Hlena Hlenb Hnr Hnrb.
  apply GInduction; auto; introns Hdis; allsimpl.

  - Case "vleaf". simpl. f_equal. rewrite DeqSym. symmetry.  rewrite DeqSym.
    destruct_head_match; cpx.
    subst.
    allsimpl. symmetry. 
    rewrite swapVarNoChange; allsimpl;
    repeat(disjoint_reasoning); cpx.
    allrewrite (@DeqTrue (VarSym G)); allsimpl;
    repeat(disjoint_reasoning).

  - Case "pnode".
    rw Hdis; simpl; auto.

  - Case "pvleaf". simpl. f_equal. rewrite DeqSym. symmetry.  rewrite DeqSym.
    destruct_head_match; cpx.
    subst.
    simpl. symmetry. apply swapVarDisjChain; auto;
    repeat(disjoint_reasoning); allsimpl;
    allrewrite (@DeqTrue (VarSym G)); allsimpl;
    repeat(disjoint_reasoning).

  - rw Hdis; simpl; auto.
  - rw Hdis; simpl; auto.
  - f_equal.
    + apply Hdis; repeat(disjoint_reasoning).
    + apply Hdis0; repeat(disjoint_reasoning).

  - f_equal.
    + apply Hdis; repeat(disjoint_reasoning).
    + apply Hdis0; repeat(disjoint_reasoning).
Qed.
*)

(*
Lemma alphaSwapEmbedCongr : forall {G : CFGV} {vc : VarSym G},
( 
  (forall (s : GSym G) (a b : Term s), tAlphaEq vc a b -> True)
   *
  (forall (s : GSym G),
      EquiVariantRelSame (@pSwapEmbed G vc s) (pAlphaEq vc))
  *
  (EquiVariantRelSame (@swapEmbedAbs G vc) (@AlphaEqAbs G vc))
  *
  (EquiVariantRelSame (@swapEmbedLAbs G vc) (@lAlphaEqAbs G vc))
).
Proof.
  intros. GAlphaInd; introns Hyp; intros; 
  allsimpl; try (econstructor; eauto with Alpha; fail);[ | |].
- Case "pembed". constructor.
  apply alphaEquiVariant; eauto.
- Case "pnode". constructor.
  unfold MakeAbstractionsPNode.
  rewrite <-  MakeLAbsSwapCommute.
  rewrite <-  MakeLAbsSwapCommute.
  cpx.

- Case "patAbs".
  specialize (Hyp4 sw).
Qed.
*)
