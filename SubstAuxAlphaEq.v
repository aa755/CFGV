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
Require Export Term.
Require Export AssociationList.
Set Implicit Arguments.
Require Export Swap.
Require Export AlphaEqProps.
Require Export SubstAux.

Definition swapSub {G : CFGV} {vc : VarSym G} 
  (sub : SSubstitution vc) (sw : Swapping vc):=
  ALMap (swapVar sw) (fun t => tSwap t sw) sub.


Lemma swapSubApp :
  forall {G : CFGV} {vc : VarSym G}
     (sub : SSubstitution vc)
    (sa sb : Swapping vc),
       swapSub (swapSub sub sa) sb
       = swapSub sub (sa ++ sb).
Proof.
  intros. induction sub; cpx;[].
  allsimpl. f_equal; sp; auto.
  simpl. f_equal;
  autorewrite with SwapAppR; refl.
Qed.

Hint Rewrite (fun G s => @swapSubApp G s) : SwapAppR.
Hint Rewrite <- (fun G s => @swapSubApp G s) : SwapAppL.

Definition allVarsSub {G : CFGV} {vc : VarSym G} 
  (sub : SSubstitution vc) :=
  flat_map (fun p => (fst p)::(tfreevars _ (snd p))) sub.


Lemma swapSubFilterCommute: 
  forall {G : CFGV} {vc : VarSym G}
    (sub : SSubstitution vc)
    (sw : Swapping vc)
    (l : list (vType vc)),
    ALFilter (DeqVtype vc) (swapSub sub sw) (swapLVar sw l)
    = swapSub (ALFilter (DeqVtype vc) sub l) sw.
Proof.
  intros.  unfold swapSub.
  rewrite <- ALEndoMapFilterCommute;[refl|].
  introv Hq; apply swapVarInj in Hq; trivial.
Qed.

Lemma swapSubRevCancel :
  forall {G : CFGV} {vc : VarSym G}
    (sub : SSubstitution vc) (sw : Swapping vc),
       swapSub sub (sw ++ (rev sw)) = sub.
Proof.
  intros. induction sub; cpx;[].
  allsimpl. f_equal; sp; auto.
  simpl. f_equal;
  autorewrite with fast;refl.
Qed.

Hint Rewrite (fun G vc 
    => (@swapSubRevCancel G vc)) : fast.

Section GramVC.
Variable G : CFGV.
Variable vc  : VarSym G.

Lemma swapSubSwitch :
    forall (sub: SSubstitution vc)(sw : Swapping vc),
       swapSub sub sw = swapSub sub (ALSwitch sw).
Proof.
  induction sub; cpx.
  intros. simpl.
  f_equal; cpx.
  f_equal.
  - apply swapVarSwitch.
  - apply swapSwitch.
Qed.

Lemma swapSubRevNoRep :
  forall (sw : Swapping vc) (sub: SSubstitution vc),
    no_repeats (ALDom sw)
    -> no_repeats (ALRange sw) 
    -> disjoint (ALDom sw) (ALRange sw)        
    -> swapSub sub sw = swapSub sub (rev sw).
Proof.
  induction sub; cpx.
  intros.
  simpl. f_equal;cpx.
  f_equal.
  - apply swapVarRevNoRep; auto.
  - apply swapRevNoRep; auto.
Qed.

Definition abindersDeep (a : Abstraction G vc) : list (vType vc) :=
  match a with
    | termAbs _ vars t =>  (tBndngVarsDeep vc t) ++ vars
    | patAbs  _ vars p =>  (pBndngVarsDeep vc p) ++ vars
  end.

Fixpoint albindersDeep (l : list (Abstraction G vc)) : list  (vType vc) :=
  match l with
    | [] => []
    | a :: l => abindersDeep a ++ albindersDeep l
  end.

Lemma subsetAlbindersDeep:
  forall {mp} (ma : Mixture mp) llb,
subset (albindersDeep (MakeAbstractions vc ma llb)) 
        ((mBndngVarsDeep vc ma) ++ flatten llb).
Proof.
  induction ma; cpx; destruct llb;
  allsimpl; autorewrite with fast in *.
  - apply subset_app_lr; eauto.
    pose proof (IHma []); autorewrite with fast in *; cpx.
  - rw <- app_assoc. rw <- app_assoc.
    apply subset_app_lr; eauto.
    eapply subset_trans;
    [|apply subsetAppEauto].
    rewrite <- app_assoc.
    apply subset_app_lr; eauto.
    eapply subset_trans;
    [cpx|apply subsetAppEauto].

  - apply subset_app_lr; eauto.
    pose proof (IHma []); autorewrite with fast in *; cpx.
  - rw <- app_assoc. rw <- app_assoc.
    apply subset_app_lr; eauto.
    eapply subset_trans;
    [|apply subsetAppEauto].
    rewrite <- app_assoc.
    apply subset_app_lr; eauto.
    eapply subset_trans;
    [cpx|apply subsetAppEauto].
Qed.

Lemma albndDeepMakeAbTSubset :
  forall (p : TermProd G) (ma : Mixture (tpRhsAugIsPat p)),
    subset 
      (albindersDeep 
        (MakeAbstractions vc ma 
            (lBoundVars vc (bndngPatIndices p) ma)))
      (mBndngVarsDeep vc ma).
Proof.
  introv.
  unfold MakeAbstractionsTNode, MakeAbstractionsTNodeAux.
  pose proof (@lBoundVarsmBndngVars _ vc _ ma (bndngPatIndices p)) as Hs. 
  pose proof (lBoundVarsLength vc ma (bndngPatIndices p)) as Hl.
  remember ((lBoundVars vc (bndngPatIndices p) ma)) as llb.
  eapply subset_trans;[apply subsetAlbindersDeep|].
  apply subset_app.
  dands; eauto.
  eauto 2 with SetReasoning.
Qed.

Hint Resolve albndDeepMakeAbTSubset : SetReasoning.


Lemma albndDeepMakeAbPSubset :
  forall p (ma : Mixture (map (fun x : GSym G => (true, x)) (ppRhsSym p))),
albindersDeep (MakeAbstractions vc ma []) = mBndngVarsDeep vc ma.
Proof.
  introv.
  unfold MakeAbstractionsPNode.
  induction ma; allsimpl; auto; introv; apply app_if; 
  autorewrite with fast; auto.
Qed.

Lemma EquivariantSSubstAux : 
    (forall {gs : GSym G}, 
    EquiVariantFn2 (@tSwap _ vc gs)
                   (@swapSub G vc)
                   (@tSwap _ vc gs)
                   (@tSSubstAux _ _ _))
    *
    (forall (gs : GSym G),
    EquiVariantFn2 (@pSwap _ vc gs)
                   (@swapSub G vc)
                   (@pSwap _ vc gs)
                   (@pSSubstAux _ _ _))
    *
    (forall (lgs : list (bool * GSym G)),
    EquiVariantFn3 (@mSwap _ vc lgs)
                   (fun x s => swapLLVar s x) 
                   (@swapSub G vc)
                   (@mSwap _ vc lgs)
                   (@mSSubstAux _ _ _)).
Proof.
GInduction; introns Hyp; allsimpl; cpx; try (intros; f_equal; cpx; fail).
- Case "vleaf".
  intros. simpl.
  destruct_head_match; allsimpl; cpx;
    [|f_equal;destruct_head_match; cpx].
  destruct e. allsimpl.
  rename tb into sub.
  unfold ALFindDef.
  assert (injective_fun (swapVar sw)) by
  (introv Hq; apply swapVarInj in Hq; trivial).

  DALFindC fsv.
  + unfold swapSub. erewrite ALFindMapSome; eauto.    
  + unfold swapSub. erewrite ALFindMapNone; eauto.
    simpl. rewrite DeqTrue. simpl. refl.

- Case "tnode".
  intros. simpl. f_equal.
  rewrite lBoundVars_swap. apply Hyp.

- Case "pnode".
  intros. simpl. f_equal. apply Hyp.

- Case "mtcons".
  intros.
  rename tb into lvb.
  destruct lvb; allsimpl; f_equal; cpx;
    [rw Hyp0; simpl; cpx|].
  rw Hyp. f_equal.
  symmetry.
  apply swapSubFilterCommute.

- Case "mpcons".
  intros.
  rename tb into lvb.
  destruct lvb; allsimpl; f_equal; cpx;
    [rw Hyp0; simpl; cpx|].
  rw Hyp. f_equal.
  symmetry.
  apply swapSubFilterCommute.
Qed.

Definition AlphaEqSubst (suba subb : SSubstitution vc) := 
  (ALRangeRel (tAlphaEq vc) suba subb).

Lemma AlphaEqSubstApp : forall
  (sla slb sra srb : SSubstitution vc),
  AlphaEqSubst sla sra
  -> AlphaEqSubst slb srb
  -> AlphaEqSubst (sla ++ slb) (sra ++ srb).
Proof.
  intros. apply ALRangeRelApp.
  dands; trivial.
Qed.

Lemma AlphaEqSubstRefl : forall
  (s : SSubstitution vc),
  AlphaEqSubst s s.
Proof.
  intros. apply ALRangeRelRefl.
  introv. eauto with Alpha.
Qed.

Lemma alphaEqAlphaSubst : 
(  (forall (s : GSym G) (t : Term s)
  (subl subr : SSubstitution vc),
       AlphaEqSubst subl subr
        -> tAlphaEq vc (tSSubstAux t subl) (tSSubstAux t subr))
   *
  (forall (s : GSym G) (pt : Pattern s)
  (subl subr : SSubstitution vc),
       AlphaEqSubst subl subr
        -> pAlphaEq vc (pSSubstAux pt subl) (pSSubstAux pt subr))
   *
  (forall (l : MixtureParam) (m : Mixture l) 
  (lbv : list (list (vType vc)))
  (subl subr : SSubstitution vc),
    AlphaEqSubst subl subr
      -> lAlphaEqAbs 
            (MakeAbstractions vc (mSSubstAux m lbv subl) lbv)
            (MakeAbstractions vc (mSSubstAux m lbv subr) lbv)
)
).

Proof.
  GInduction; introns Hyp; intros; cpx; allsimpl;
  try dlist_len lbv;  try (econstructor; eauto with slow; fail).
- Case "vleaf".
  ddeq; sp;[| eauto with Alpha; fail].
  destruct e. simpl. unfold ALFindDef.
  dalfind.
  + eapply ALRangeRelFind in h; eauto.
    exrepnd. rw h2. sp.
  + repnud Hyp. apply ALRangeRelSameDom in Hyp.
    rewrite Hyp in h0.
    dalfind; cpx;[| eauto with Alpha; fail].
    apply ALInEta in h2. dands; cpx.

- Case "tnode". constructor. allunfold mAlphaEq.
  unfold MakeAbstractionsTNode.
  unfold MakeAbstractionsTNodeAux.
  unfold allBndngVars.
   rewrite <- lBoundVarsSameSSubstAux.
  rewrite <- lBoundVarsSameSSubstAux.
  cpx.

- Case "mtcons". destruct lbv; cpx.
  + allsimpl. constructor; cpx.
    eauto with Alpha.
  + allsimpl. constructor; cpx.
    apply AlphaEqNilAbsT.
    apply Hyp. apply ALRangeRelFilter.
    trivial.

- Case "mpcons". destruct lbv; cpx.
  + allsimpl. constructor; cpx.
    eauto with Alpha.
  + allsimpl. constructor; cpx.
    apply AlphaEqNilAbsP.
    apply Hyp. apply ALRangeRelFilter.
    trivial.
Qed.


Definition aSSubstAux
           (a : Abstraction G vc)
           (sub : SSubstitution vc) : Abstraction G vc :=
match a with
| termAbs _ vars t 
  => termAbs _ vars (tSSubstAux t (SubFilter sub vars))
| patAbs  _ vars p 
  => patAbs  _ vars (pSSubstAux p (SubFilter sub vars))
end.

Fixpoint alSSubstAux
         (l : list (Abstraction G vc))
         (sub : SSubstitution vc) : list (Abstraction G vc) :=
  match l with
    | [] => []
    | a :: l => aSSubstAux a sub :: alSSubstAux l sub
  end.


Lemma alSSubstAux_MakeAbstractionsTNode :
  forall p ma sub,
    alSSubstAux (MakeAbstractionsTNode vc p ma) sub
    = MakeAbstractions vc
  (mSSubstAux ma (lBoundVars vc (bndngPatIndices p) ma) sub)
  (lBoundVars vc (bndngPatIndices p)
     (mSSubstAux ma (lBoundVars vc (bndngPatIndices p) ma) sub)).
Proof.
  unfold MakeAbstractionsTNode, MakeAbstractionsTNodeAux.
  intros p ma sub.
  rw <- lBoundVarsSameSSubstAux.
  remember (lBoundVars vc (bndngPatIndices p) ma).
  clear Heql.
  revert l sub.
  induction ma; introv; allsimpl; auto;
  destruct l; allsimpl; auto;
  unfold SubFilter;
  try (rw ALFilter_nil_r);
  apply eq_cons; auto.
Qed.
Lemma alSSubstAux_MakeAbstractionsPNode :
forall (p : PatProd G)
  (ma : Mixture (map (fun x : GSym G => (true, x)) (ppRhsSym p)))
  (sub : SSubstitution vc),
alSSubstAux (MakeAbstractions vc ma []) sub =
MakeAbstractions vc (mSSubstAux ma [] sub) [].
Proof.
  induction ma; introv; allsimpl; auto;
  unfold SubFilter;
  try (rw ALFilter_nil_r); simpl;
  apply eq_cons; auto.
Qed.



Lemma subSwapAlpha:
  forall (sw : Swapping vc) (sub : SSubstitution vc),
  disjoint (ALDom sub ++ rangeFreeVars sub) (ALDom sw ++ ALRange sw)
  -> AlphaEqSubst sub (swapSub sub sw).
Proof.
  induction sub as [| (v,t) sub Hind]; cpx.
  introv Hdis. allsimpl.
  rewrite rangeFreeVars_cons in Hdis.
  repeat (disjoint_reasoning).
  allsimpl.
  constructor;
    [symmetry; apply swapVarNoChange; cpx|].
  dands; cpx.
  - apply alphaEqSwapNonFree.
    apply leavesLVarUnchanged1; repeat (disjoint_reasoning).
  - apply Hind; repeat (disjoint_reasoning).
Qed.
    
    
  
Lemma SubstFilterDisjAux: 
  forall sub lbva lbcnew,
  disjoint (lbva ++ lbcnew) (rangeFreeVars sub)
  -> disjoint lbcnew (ALDom sub)
  -> 
  disjoint
    (ALDom (ALFilter (DeqVtype vc) sub lbva) ++
        rangeFreeVars (ALFilter (DeqVtype vc) sub lbva)) 
    (lbva ++ lbcnew).
Proof.
  introv H1d H2d.
  rewrite  <- ALDomFilterCommute.
  repeat(disjoint_reasoning); cpx.
  - apply disjoint_diff_l. rewrite diffSameNil. auto.
  - SetReasoning.
  - apply disjoint_diff_l. SetReasoning.
    apply subset_diff. SetReasoning.
  - clear H2d. SetReasoning.
Qed.

Lemma rangeFreeVarsEquivariant : 
    EquiVariantFn (@swapSub _ vc)
      (fun x s => swapLVar s x) 
      (@rangeFreeVars _ _ ).
Proof.
  unfold EquiVariantFn.
  intros sub sw.
  induction sub as [| (v,t) sub Hind]; cpx.
  allsimpl. rw rangeFreeVars_cons.
  rw rangeFreeVars_cons.
  rewrite swapLVar_app.
  f_equal;cpx.
  rewrite (tcase freevarsEquivariant).
  refl.
Qed.

Lemma SubstAuxRespectsAlpha :
(
  (forall (gs : GSym G) (ta tb : Term gs),
     tAlphaEq vc ta tb
     -> forall (sub : SSubstitution vc),
          tAlphaEq vc ta tb
          -> disjoint (tBndngVarsDeep vc ta++tBndngVarsDeep vc tb) (rangeFreeVars sub)
          -> tAlphaEq vc (@tSSubstAux G vc gs ta sub) (tSSubstAux tb sub))
  *
  (forall (gs : GSym G) (pa pb : Pattern gs),
     pAlphaEq vc pa pb
     -> forall (sub : SSubstitution vc),
          pAlphaEq vc pa pb
          -> disjoint (pBndngVarsDeep vc pa++pBndngVarsDeep vc pb) (rangeFreeVars sub)
          -> pAlphaEq vc (@pSSubstAux G vc gs pa sub) (pSSubstAux pb sub))
  *
  (forall aa ab,
     AlphaEqAbs aa ab
     -> forall (sub : SSubstitution vc),
          AlphaEqAbs aa ab
          -> disjoint (abindersDeep aa++abindersDeep ab) (rangeFreeVars sub)
          -> AlphaEqAbs (aSSubstAux aa sub) (aSSubstAux ab sub))
  *
  (forall la lb,
     lAlphaEqAbs la lb
     -> forall (sub : SSubstitution vc),
          lAlphaEqAbs la lb
          -> disjoint (albindersDeep la++albindersDeep lb) (rangeFreeVars sub)
          -> lAlphaEqAbs (alSSubstAux la sub) (alSSubstAux lb sub))
).
Proof.
  intros.
  GAlphaInd; introns Hyp; intros; allsimpl; cpx; eauto with Alpha;
  try constructor.
- Case "tnode".
  allrw <- alSSubstAux_MakeAbstractionsTNode; auto.
  apply Hyp0; auto;repeat(disjoint_reasoning).
  + hide_hyp Hyp2. 
    SetReasoning. unfold allBndngVars.
    eauto 3 with SetReasoning.

  + hide_hyp Hyp3. unfold allBndngVars.
    eauto 3 with SetReasoning.

- Case "pembed". apply Hyp0; auto.

- Case "pnode".
  allrw <- alSSubstAux_MakeAbstractionsPNode.
  apply Hyp0; auto; repeat(disjoint_reasoning);
  rewrite albndDeepMakeAbPSubset; auto.

- Case "termAbs". 
  rename Hyp5 into Htal.
  apply (betterAbsTElim (lbnew 
        ++ lbva
        ++ (ALDom sub)
        ++ (rangeFreeVars sub)
        ++ (tBndngVarsDeep vc tma)
        ++ (tBndngVarsDeep vc tmb)
        ++ (tfreevars vc tma)
        ++ (tfreevars vc tmb)
        ++ tAllVars (tSSubstAux tma (ALFilter (DeqVtype vc) sub lbva))
        ++ tAllVars (tSSubstAux tmb (ALFilter (DeqVtype vc) sub lbvb))
     )) in Htal.
  allsimpl. exrepnd.
  rename lbnew0 into lbcnew.
  (** we need to prepare lhs and rhs of [Htal0] 
   so that it can match
    the inductive hypothessis [Hyp4].*)
  apply (tcase alphaEquiVariant ) in Htal0.
  specialize (Htal0 (combine lbcnew lbnew)).
  rewrite (tcase swap_app) in Htal0.
  rewrite (tcase swap_app) in Htal0.
  unfold tFresh in Htal3.
  unfold tFresh in Hyp1.
  allsimpl. repnd.
  match type of Htal0 with
  tAlphaEq _ _ ?r => remember r as ll
  end.
  autorewrite with slow in Htal0; try congruence;
  cpx; repeat (disjoint_reasoning).
  subst ll.
  autorewrite with slow in Htal0; try congruence;
  cpx; repeat (disjoint_reasoning).
  (** [sub] wont work because [lbnew] is not 
      required to be disjoint from freevars of [sub].
      Swapping [sub] with [(combine lbnew lbcnew)] would
      definately meet that disjointness requirement.*)
  apply Hyp4 with 
      (sub:= swapSub sub (combine lbnew lbcnew)) in Htal0.
  + apply alAbT with (lbnew:=lbcnew); try congruence;
    [unfolds_base; simpl; dands | | ]; cpx;
    repeat (disjoint_reasoning);[].
    (** need to cance the swapping of [sub] in Htal0 *)
    apply (tcase alphaEquiVariant ) in Htal0.
    specialize (Htal0 (combine lbnew lbcnew)).
    rewrite (tcase EquivariantSSubstAux) in Htal0.
    rewrite (tcase EquivariantSSubstAux) in Htal0.
    rewrite (tcase swap_app) in Htal0.
    rewrite (tcase swap_app) in Htal0.
    autorewrite with slow in Htal0; try congruence;
    cpx; repeat (disjoint_reasoning).

    rewrite swapSubRevNoRep in Htal0; auto;
    autorewrite with fast; cpx.
    autorewrite with SwapAppR in Htal0.
    autorewrite with fast in Htal0.

    (** some work in the conclusion  *)
    rewrite (tcase EquivariantSSubstAux).
    rewrite (tcase EquivariantSSubstAux).

    (** Now, we need to make [Htal0] look like the conclusion.
        First add the filtering *)
    rewrite (fun G S => tcase ( SSubstAuxSubFilter G S)) 
      with (lf:= lbva) in Htal0 by
      (rewrite <- (tcase freevarsEquivariant);
       apply swapLVarDisjoint2; auto).

    remAlphaLeft Htal0 ll.
    rewrite (fun G S => tcase ( SSubstAuxSubFilter G S)) 
      with (lf:= lbvb) in Htal0 by
      (rewrite <- (tcase freevarsEquivariant);
       apply swapLVarDisjoint2; auto).

    subst ll.
    
    (** At this point, the proof looked hopeless.
        The filtered [sub] in the conclusion 
        is swapped by different swappings on both side. 
        Equivariance can only allow putting the same swapping.
        Also, the term part of SSubstAux is already matched.
        Using equivariance will only spoil that matching.

        The key insight is that [lbva] and [lbvb] are
        disjoint from the freevars of the range of the
        substition. The lemma [subSwapAlpha] says that swapping
        a substition with a swapping disjoint from
        the free vars of its range results in an alpha
        equal substitition.
        
        The lemma [alphaEqAlphaSubst] already allows
        us to change to an alpha equal substitution
        upto alpha equality
    *)
    dimp (subSwapAlpha (combine lbva lbcnew)
                        (SubFilter sub lbva));
    [ autorewrite with fast; try congruence;
      apply SubstFilterDisjAux; cpx;
     repeat(disjoint_reasoning)|].

    dimp (subSwapAlpha (combine lbvb lbcnew) 
                       (SubFilter sub lbvb));
    [ autorewrite with fast; try congruence;
      apply SubstFilterDisjAux; cpx;
     repeat(disjoint_reasoning)|].
    remember (tSwap tma (combine lbva lbcnew)) as tmsa.
    remember (tSwap tmb (combine lbvb lbcnew)) as tmsb.
    remember (SubFilter sub lbva) as sfa.
    remember (SubFilter sub lbvb) as sfb.
    pose proof ((tcase alphaEqAlphaSubst) _ tmsa  _ _ hyp).
    pose proof ((tcase alphaEqAlphaSubst) _ tmsb  _ _ hyp0).
    repeat match goal with
    | [H : disjoint _ _ |- _] => clear H
    | [H : no_repeats _  |- _] => clear H
    | [H :_ = _ |- _] => clear H
    end.
    clear Hyp4 Hyp3 hyp hyp0.
    apply (tcase alphaEqSym) in X.
    eapply  (tcase alphaEqTransitive).
    apply X.
    eapply  (tcase alphaEqTransitive).
    apply Htal0.
    auto.
  + rewrite <- (tcase bndngVarsDeepEquivariant).
    rewrite <- (tcase bndngVarsDeepEquivariant).
    rewrite <- rangeFreeVarsEquivariant.
    eapply subset_disjoint_r
    with (l3 := (tBndngVarsDeep vc tmb))  in Hyp8;
     eauto 2 with SetReasoning;[].

    eapply subset_disjoint_r
    with (l3 := (tBndngVarsDeep vc tma))  in Hyp7;
     eauto 2 with SetReasoning;[].
     (** this is too complicated to deal with.
          We will cancel the swapping in the RHS to
          simplify the reasoning *)
    apply DisjointEquivariantRev with (sw:= (combine lbnew lbcnew)).
    match goal with
    [|- disjoint ?l _] => remember l as ld
    end.
    rewrite swapLVarRevNoRep; auto;
    autorewrite with fast; cpx.
    autorewrite with SwapAppR.
    autorewrite with fast.
    subst.
    rewrite swapLVar_app.
    rewrite  swapLVarApp.
    rewrite  swapLVarApp.
    autorewrite with slow; try congruence;
    cpx; repeat (disjoint_reasoning);
    apply disjointSwapLVar;
    autorewrite with fast; try congruence;
    repeat (disjoint_reasoning).
- Case "patAbs". (** exactly same as [termAbs] case *)
  rename Hyp5 into Htal.
  apply (betterAbsPElim (lbnew 
        ++ lbva
        ++ (ALDom sub)
        ++ (rangeFreeVars sub)
        ++ (pBndngVarsDeep vc tma)
        ++ (pBndngVarsDeep vc tmb)
        ++ (pfreevars vc tma)
        ++ (pfreevars vc tmb)
        ++ pAllVars (pSSubstAux tma (ALFilter (DeqVtype vc) sub lbva))
        ++ pAllVars (pSSubstAux tmb (ALFilter (DeqVtype vc) sub lbvb))
     )) in Htal.
  allsimpl. exrepnd.
  rename lbnew0 into lbcnew.
  (** we need to prepare lhs and rhs of [Htal0] 
   so that it can match
    the inductive hypothessis [Hyp4].*)
  apply (tcase alphaEquiVariant ) in Htal0.
  specialize (Htal0 (combine lbcnew lbnew)).
  rewrite (pcase swap_app) in Htal0.
  rewrite (pcase swap_app) in Htal0.
  unfold pFresh in Htal3.
  unfold pFresh in Hyp1.
  allsimpl. repnd.
  match type of Htal0 with
  pAlphaEq _ _ ?r => remember r as ll
  end.
  autorewrite with slow in Htal0; try congruence;
  cpx; repeat (disjoint_reasoning).
  subst ll.
  autorewrite with slow in Htal0; try congruence;
  cpx; repeat (disjoint_reasoning).
  apply Hyp4 with 
      (sub:= swapSub sub (combine lbnew lbcnew)) in Htal0.
  + apply alAbP with (lbnew:=lbcnew); try congruence;
    [unfolds_base; simpl; dands | | ]; cpx;
    repeat (disjoint_reasoning);[].
    apply (tcase alphaEquiVariant ) in Htal0.
    specialize (Htal0 (combine lbnew lbcnew)).
    rewrite (pcase EquivariantSSubstAux) in Htal0.
    rewrite (pcase EquivariantSSubstAux) in Htal0.
    rewrite (pcase swap_app) in Htal0.
    rewrite (pcase swap_app) in Htal0.
    autorewrite with slow in Htal0; try congruence;
    cpx; repeat (disjoint_reasoning).

    rewrite swapSubRevNoRep in Htal0; auto;
    autorewrite with fast; cpx.
    autorewrite with SwapAppR in Htal0.
    autorewrite with fast in Htal0.

    rewrite (pcase EquivariantSSubstAux).
    rewrite (pcase EquivariantSSubstAux).
    rewrite (fun G S => pcase ( SSubstAuxSubFilter G S)) 
      with (lf:= lbva) in Htal0 by
      (rewrite <- (pcase freevarsEquivariant);
       apply swapLVarDisjoint2; auto).

    remAlphaLeft Htal0 ll.
    rewrite (fun G S => pcase ( SSubstAuxSubFilter G S)) 
      with (lf:= lbvb) in Htal0 by
      (rewrite <- (pcase freevarsEquivariant);
       apply swapLVarDisjoint2; auto).

    subst ll.
    dimp (subSwapAlpha (combine lbva lbcnew)
                        (SubFilter sub lbva));
    [ autorewrite with fast; try congruence;
      apply SubstFilterDisjAux; cpx;
     repeat(disjoint_reasoning)|].

    dimp (subSwapAlpha (combine lbvb lbcnew) 
                       (SubFilter sub lbvb));
    [ autorewrite with fast; try congruence;
      apply SubstFilterDisjAux; cpx;
     repeat(disjoint_reasoning)|].
    remember (pSwap tma (combine lbva lbcnew)) as tmsa.
    remember (pSwap tmb (combine lbvb lbcnew)) as tmsb.
    remember (SubFilter sub lbva) as sfa.
    remember (SubFilter sub lbvb) as sfb.
    pose proof ((pcase alphaEqAlphaSubst) _ tmsa  _ _ hyp).
    pose proof ((pcase alphaEqAlphaSubst) _ tmsb  _ _ hyp0).
    repeat match goal with
    | [H : disjoint _ _ |- _] => clear H
    | [H : no_repeats _  |- _] => clear H
    | [H :_ = _ |- _] => clear H
    end.
    clear Hyp4 Hyp3 hyp hyp0.
    apply (tcase alphaEqSym) in X.
    eapply  (tcase alphaEqTransitive).
    apply X.
    eapply  (tcase alphaEqTransitive).
    apply Htal0.
    auto.
  + rewrite <- (pcase bndngVarsDeepEquivariant).
    rewrite <- (pcase bndngVarsDeepEquivariant).
    rewrite <- rangeFreeVarsEquivariant.
    eapply subset_disjoint_r
    with (l3 := (pBndngVarsDeep vc tmb))  in Hyp8;
     eauto 2 with SetReasoning;[].

    eapply subset_disjoint_r
    with (l3 := (pBndngVarsDeep vc tma))  in Hyp7;
     eauto 2 with SetReasoning;[].
    apply DisjointEquivariantRev with (sw:= (combine lbnew lbcnew)).
    match goal with
    [|- disjoint ?l _] => remember l as ld
    end.
    rewrite swapLVarRevNoRep; auto;
    autorewrite with fast; cpx.
    autorewrite with SwapAppR.
    autorewrite with fast.
    subst.
    rewrite swapLVar_app.
    rewrite  swapLVarApp.
    rewrite  swapLVarApp.
    autorewrite with slow; try congruence;
    cpx; repeat (disjoint_reasoning);
    apply disjointSwapLVar;
    autorewrite with fast; try congruence;
    repeat (disjoint_reasoning).

- apply Hyp0; repeat(disjoint_reasoning).
- apply Hyp2; repeat(disjoint_reasoning).
Qed.

Lemma subAlphaSameFV:
  forall (suba subb : SSubstitution vc),
  AlphaEqSubst suba subb
  -> rangeFreeVars suba = rangeFreeVars subb. 
Proof.
  induction suba as [| (va,ta) suba Hind]; introv Hal;
  destruct subb as [| (vb,tb) subb];
  repnud Hal; simpl in Hal; cpx.
  repnd. rw rangeFreeVars_cons.
  rw rangeFreeVars_cons.
  f_equal; cpx.
  apply (ALtcase alpha_preserves_free_vars).
  trivial.
Qed.

Lemma SubstAuxRespectsAlpha2 :
forall (gs : GSym G) (ta tb : Term gs)
      (suba subb : SSubstitution vc),
      tAlphaEq vc ta tb
      -> AlphaEqSubst suba subb
      -> disjoint (tBndngVarsDeep vc ta) (rangeFreeVars suba)
      -> disjoint (tBndngVarsDeep vc tb) (rangeFreeVars subb)
      -> tAlphaEq vc (tSSubstAux ta suba) 
                     (tSSubstAux tb subb).
Proof.
  introns Hyp.
  rewrite subAlphaSameFV
    with (subb:=subb)  in Hyp1; eauto with Alpha;[].
  duplicate Hyp.
  apply (ALtcase SubstAuxRespectsAlpha)
      with (sub:= subb) in Hyp; cpx;
      [|repeat (disjoint_reasoning); fail].
  pose proof (tcase alphaEqAlphaSubst gs ta _ _ Hyp0).
  eauto with Alpha.
Qed.

End GramVC.

Hint Resolve AlphaEqSubstRefl : Alpha.


(*Hint Resolve albindersDeepSubset : SetReasoning.*)

(*
Lemma swapSubDisjChain : 
  forall  {G : CFGV} {vc : VarSym G}
  (vsa vs vsb : list (vType vc))
  (sub : SSubstitution vc),
    length vs = length vsa
    -> length vs = length vsb
    -> no_repeats vs
    -> no_repeats vsb
    -> disjoint vs (vsa ++ vsb ++ (allVarsSub sub))
    -> disjoint vsb (vsa ++ (allVarsSub sub))
    -> swapSub sub ((combine vsa  vs) ++  (combine vs  vsb))
       = swapSub sub (combine vsa  vsb).
Admitted.
*)
