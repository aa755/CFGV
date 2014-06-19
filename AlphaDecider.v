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
Require Export AlphaEqProps.



Ltac EqDecRefl :=
  let dec:= fresh "dec" in
  let HH:= fresh "Hrefl" in
repeat match goal with
[pp : @eq ?T ?ta ?tb |- _ ] => 
  assert (Deq T) as dec by eauto with Deq;
  pose proof (UIPReflDeq dec _ pp) as HH;
  try rewrite HH; clear HH dec
end.

Ltac EqDec ta tb :=
  let dec:= fresh "dec" in
  let Heq:= fresh "Heq" ta tb in
  let Hneq:= fresh "Hneq" ta tb in
  let T := type of ta in
  assert (Deq T) as dec by eauto with Deq;
  destruct (dec ta tb) as [Heq| Hneq]; clear dec.


Definition tAlphaEqG {G} (sa sb : GSym G) 
  (vc: VarSym G ) (ta : Term sa) (tb : Term sb):=
match (deqGSym sa sb) with
| left eqq => tAlphaEq vc (transport eqq ta) tb
| right eqq => False
end.

Definition pAlphaEqG {G} (sa sb : GSym G) 
  (vc: VarSym G ) (ta : Pattern sa) (tb : Pattern sb):=
match (deqGSym sa sb) with
| left eqq => pAlphaEq vc (transport eqq ta) tb
| right eqq => False
end.

Ltac notAlpha :=
  let Halc := fresh "Halc" in
  let AlphaTac := introv Halc;
    inverts Halc;
    EqDecSndEq;
    subst;
    contradiction in
  let Hseq := fresh  "Hseq" in
  let Hseqd := fresh  "Hseqd" in
  try(AlphaTac);
  unfold  tAlphaEqG; unfold  pAlphaEqG;
  match goal with
  [|- context [deqGSym ?l ?l]] =>
    rewrite DeqTrue; simpl; AlphaTac
  | [|- context [deqGSym ?l ?r]] =>
    destruct (deqGSym l r) as [Hseq |?]; cpx;
    duplicate Hseq as Hseqd;
    inverts Hseq; cpx ; try subst; cpx
  end.

Lemma decideAbsT {G} (vc : VarSym G) 
  (sa : GSym G) (ta: Term sa)
(Hdt : forall phnew : Term sa,
      tSize phnew <= tSize ta ->
      forall (sb : GSym G) (tb : Term sb), 
     decidable (tAlphaEqG vc phnew tb))
(sb : GSym G) (tb: Term sa)
(la lb :(list (vType vc))) :
decidable (AlphaEqAbs (termAbs vc la ta) (termAbs vc lb tb)).
Proof.
  remember (beq_nat (length la) (length lb)) as blen.
  destruct blen;
    [
        applysym beq_nat_true in Heqblen
      | 
        right ;
        applysym beq_nat_false in Heqblen;
        introv Hal; inverts Hal;
        EqDecSndEq; omega
    ].
  remember (GFreshVars (la++lb
              ++ tAllVars ta++tAllVars tb) la) as lvn.
  remember (tSwap ta (combine la lvn)) as phnew.
  pose proof (tcase 
        (@swapPreservesSize G vc (combine la lvn)) _ ta) as Hs.
  specialize (Hdt (tSwap ta (combine la lvn))).
  rewrite Hs in Hdt.
  dimp Hdt. apply Hdt with 
        (tb:= (tSwap tb (combine lb lvn))) in hyp.
  unfold tAlphaEqG in hyp.
  rewrite DeqTrue in hyp. allsimpl.
  clear Hs  Hdt.
  clear dependent phnew.
  destruct hyp as [? | Hnal];[left| right];
  pose proof (FreshDistVarsSpec 
      (la ++ lb ++ tAllVars ta ++ tAllVars tb) la ) as XX;
  rewrite <- Heqlvn in XX;
  simpl in XX; repnd; dands;
  symmetry in XX.
  - apply alAbT with (lbnew:=lvn); 
        cpx; try congruence;
    unfold tFresh; allsimpl; repeat(disjoint_reasoning).
  - introv Hal. apply Hnal. clear Hnal. clear Heqlvn.
    apply betterAbsTElim 
    with (lvAvoid:= lvn) in Hal.
     allsimpl. exrepnd.
    apply tAlphaEqEquivariantRev with 
    (sw := combine lvn lbnew).
    autorewrite with SwapAppR.
    unfold tFresh in Hal3.
    allsimpl. repnd.
    symmetry in XX.
    autorewrite with slow; try congruence;
    cpx; repeat (disjoint_reasoning);
    repeat match goal with
    [ H : disjoint _ _ |- _ ] => clear H
    | [ H : no_repeats _ _ |- _ ] => clear H
    end.
Defined.


Lemma decideAbsP {G} (vc : VarSym G) 
  (sa : GSym G) (ta: Pattern sa)
(Hdt : forall phnew : Pattern sa,
      pSize phnew <= pSize ta ->
      forall (sb : GSym G) (tb : Pattern sb),
        decidable (pAlphaEqG vc phnew tb))
(sb : GSym G) (tb: Pattern sa)
(la lb :(list (vType vc))) :
decidable (AlphaEqAbs (patAbs vc la ta) (patAbs vc lb tb)).
Proof.
  remember (beq_nat (length la) (length lb)) as blen.
  destruct blen;
    [
        applysym beq_nat_true in Heqblen
      | 
        right ;
        applysym beq_nat_false in Heqblen;
        introv Hal; inverts Hal;
        EqDecSndEq; omega
    ].
  remember (GFreshVars (la++lb
              ++ pAllVars ta++pAllVars tb) la) as lvn.
  remember (pSwap ta (combine la lvn)) as phnew.
  pose proof (pcase 
        (@swapPreservesSize G vc (combine la lvn)) _ ta) as Hs.
  specialize (Hdt (pSwap ta (combine la lvn))).
  rewrite Hs in Hdt.
  dimp Hdt. apply Hdt with 
        (tb:= (pSwap tb (combine lb lvn))) in hyp.
  unfold pAlphaEqG in hyp.
  rewrite DeqTrue in hyp. allsimpl.
  clear Hs  Hdt.
  clear dependent phnew.
  destruct hyp as [? | Hnal];[left| right];
  pose proof (FreshDistVarsSpec 
      (la ++ lb ++ pAllVars ta ++ pAllVars tb) la ) as XX;
  rewrite <- Heqlvn in XX;
  simpl in XX; repnd; dands;
  symmetry in XX.
  - apply alAbP with (lbnew:=lvn); 
        cpx; try congruence;
    unfold pFresh; allsimpl; repeat(disjoint_reasoning).
  - introv Hal. apply Hnal. clear Hnal. clear Heqlvn.
    apply betterAbsPElim 
    with (lvAvoid:= lvn) in Hal.
     allsimpl. exrepnd.
    apply pAlphaEqEquivariantRev with 
    (sw := combine lvn lbnew).
    autorewrite with SwapAppR.
    unfold pFresh in Hal3.
    allsimpl. repnd.
    symmetry in XX.
    autorewrite with slow; try congruence;
    cpx; repeat (disjoint_reasoning);
    repeat match goal with
    [ H : disjoint _ _ |- _ ] => clear H
    | [ H : no_repeats _ _ |- _ ] => clear H
    end.
Defined.

Definition diffVarClasses{G} {sa : GSym G} (ta: Term sa)
            {sb: GSym G} (tb : Term sb) :=
match (ta, tb) with
| (vleaf vca va, vleaf vcb vb) 
    => match (DeqVarSym vca vcb) with
      |left _ => False
      |right _ => True
      end
| _ => False
end.

Definition diffPVarClasses{G} 
        {sa : GSym G} (ta: Pattern sa)
        {sb: GSym G} (tb : Pattern sb) :=
match (ta, tb) with
| (pvleaf vca va, pvleaf vcb vb) 
    => match (DeqVarSym vca vcb) with
      |left _ => False
      |right _ => True
      end
| _ => False
end.


Definition diffTProdsNode {G} {sa : GSym G} (ta: Term sa)
            {sb: GSym G} (tb : Term sb) :=
match (ta, tb) with
| (tnode pa va, tnode pb vb) 
    => match (deqPr G pa pb) with
      |left _ => False
      |right _ => True
      end
| _ => False
end.

Definition diffPProdsNode {G} {sa : GSym G} 
        (ta: Pattern sa)
            {sb: GSym G} (tb : Pattern sb) :=
match (ta, tb) with
| (pnode pa va, pnode pb vb) 
    => match (deqPPr G pa pb) with
      |left _ => False
      |right _ => True
      end
| _ => False
end.

Definition diffEmbedNode {G} {sa : GSym G} 
        (ta: Pattern sa)
            {sb: GSym G} (tb : Pattern sb) :=
match (ta, tb) with
| (embed pa va, embed pb vb) 
    => match (deqEm G pa pb) with
      |left _ => False
      |right _ => True
      end
| _ => False
end.


Definition isVLeaf {G} {sa : GSym G} (ta: Term sa) :=
match ta with
| vleaf vca va 
    => True
| _ => False
end.

Definition isPNode {G} {sa : GSym G} 
  (ta: Pattern sa) :=
match ta with
| pnode vca va 
    => True
| _ => False
end.

Definition isEmbed {G} {sa : GSym G} 
  (ta: Pattern sa) :=
match ta with
| embed vca va 
    => True
| _ => False
end.


Lemma alphaEqDecidable : forall {G} (vc : VarSym G),
     (  (forall (sa : GSym G) (ta: Term sa)
            (sb: GSym G) (tb : Term sb),
           decidable (tAlphaEqG vc ta tb))
         *
        (forall (sa : GSym G) (ta: Pattern sa)
            (sb: GSym G) (tb : Pattern sb),
            decidable (pAlphaEqG vc ta tb))
         *
        (forall (l : MixtureParam) (ma mb : Mixture l) 
        (lbva : list (list (vType vc)))
        (lbvb : list (list (vType vc))),
           decidable 
              (lAlphaEqAbs (MakeAbstractions vc ma lbva) 
                           (MakeAbstractions vc mb lbvb)))).
Proof.
  intros.
  GInductionS; introns Hyp; intros;  allsimpl.
- Case "tleaf".
  destruct tb;[ | right; notAlpha | right; notAlpha];[].
  
  EqDec T T0; [| right; notAlpha]; subst.
  EqDec t t0; [left|right]; subst;
  unfold tAlphaEqG; try rewrite DeqTrue; allsimpl;
  eauto with Alpha;[]; notAlpha.

- Case "vleaf".
  destruct tb; [right; notAlpha | |].
  + EqDec vc0 vc1;[| right]; subst; try EqDecRefl; simpl.
    * EqDec v v0; [left|right]; subst; unfolds_base;
      try rewrite DeqTrue;
      eauto with Alpha.
      notAlpha.

    * notAlpha.
      revert Hseqd0.
      remember (vleaf vc0 v) as vvl.
      remember (vleaf vc1 v0) as vvr.
      assert ( diffVarClasses vvl vvr) as Hdd
       by (subst; unfold diffVarClasses;
          cases_if; cpx).
      clear Heqvvr Heqvvl.
      remember (vSubstType G vc0).
      remember (vSubstType G vc1).
      generalize dependent vvl.
      generalize dependent vvr.
      rewrite H0.
      intros. allsimpl.
      EqDecRefl. simpl.
      clear dependent t.
      clear Hneqvc0vc1.
      clear v0 v vc0 Heqt0 Hseqd0 vc1. introv Hc; inverts Hc;
      EqDecSndEq; subst vvl; subst vvr; repnud Hdd; allsimpl; cpx.
      rewrite DeqTrue in Hdd.
      trivial.
  + right. notAlpha.
    introv Hal. inverts Hal.
    EqDecSndEq.
    GC. clear H6. clear X. clear H0.
    generalize dependent H3. 
    remember (vleaf vc0 v) as xx.
    assert (isVLeaf xx) as Hxx by (subst;simpl; auto).
    clear Heqxx.
    generalize dependent xx.
    rewrite Hseqd0. 
    allsimpl.
    introv Hisv Heq.
    inverts Heq.
    cpx.
- Case "tnode".
  destruct tb; [right; notAlpha;fail | |].

    right. notAlpha;
    remember (vleaf vc0 v) as xx.
    assert (isVLeaf xx) as Hxx by (subst;simpl; auto).
    clear Heqxx.
    generalize dependent xx.
    rewrite <- Hseqd0. 
    allsimpl.
    introv Hisv Heq.
    inverts Heq. EqDecSndEq. subst xx.
    cpx; fail.

    EqDec p p0;[| right].
    Focus 2. notAlpha.
    introv Hal.

    remember (tnode p m) as vvl.
    remember (tnode p0 m0) as vvr.
    assert (diffTProdsNode vvl vvr) as Hdd
     by (subst; unfold diffTProdsNode;
        cases_if; cpx).
    clear Heqvvr Heqvvl.
    remember (tpLhs G p).
    remember (tpLhs G p0).
    generalize dependent vvl.
    generalize dependent vvr.
    generalize Hseqd0.
    rewrite H0.
    introv. allsimpl.
    EqDecRefl. simpl.
    clear dependent t.
    introv Hta Hdd.
    clear Hseqd1 Heqt0  Hneqpp0 m0 Hyp m.
    inverts Hta;
    EqDecSndEq;
    subst vvl; subst vvr; repnud Hdd; allsimpl; cpx.
    rewrite DeqTrue in Hdd;
    trivial; fail.


  (* back to the real business *)
  subst p0. unfold tAlphaEqG.
  rewrite DeqTrue.
  simpl. rename m0 into mb.
  destruct (Hyp mb (allBndngVars vc p m) (allBndngVars vc p mb)) as
    [Hleq | Hnleq];[left; constructor;auto | right; notAlpha].
      
- Case "ptleaf".
  destruct tb;[ | right; notAlpha 
                | right; notAlpha 
                | right; notAlpha]; [].
  
  EqDec T T0; [| right; notAlpha]; subst;[].
  EqDec t t0; [left|right]; subst;
  unfold pAlphaEqG; try rewrite DeqTrue; allsimpl;
  eauto with Alpha;[]; notAlpha.
    
- Case "pvleaf".
  destruct tb;[ right; notAlpha | 
                | right; notAlpha 
                | right; notAlpha]; [].
  EqDec vc0 vc1;[ left;subst; try EqDecRefl; simpl;
                  unfold pAlphaEqG; rewrite DeqTrue
                  ; constructor; fail
                | right; notAlpha].
    
- Case "pembed".
  destruct tb;[ right; notAlpha 
                | right; notAlpha |
                | right; notAlpha].

  Focus 2.
    introv Hal. inverts Hal.
    EqDecSndEq.
    GC. clear H6. clear X. clear H0.
    generalize dependent H3.
    remember (embed p t) as xx.
    assert (isEmbed xx) as Hxx by (subst;simpl; auto).
    clear Heqxx.
    generalize dependent xx.
    rewrite Hseqd0. 
    allsimpl.
    introv Hisv Heq.
    inverts Heq.
    cpx; fail.


  EqDec p p0;[ subst p0; unfold pAlphaEqG; rewrite DeqTrue
               | right; notAlpha].
  Focus 2.
    remember (embed p t) as vvl.
    remember (embed p0 t0) as vvr.
    assert (diffEmbedNode vvl vvr) as Hdd
     by (subst; unfold diffEmbedNode;
        cases_if; cpx).
    clear Heqvvr Heqvvl.
    remember (epLhs G p).
    remember (epLhs G p0).
    generalize dependent vvl.
    generalize dependent vvr.
    generalize Hseqd0.
    rewrite H0.
    introv. allsimpl.
    EqDecRefl. simpl.
    clear dependent p.
    introv Hta Hdd.
    clear H0 Hseqd1 Hseqd0 Heqp2 p1 t0 p0.
    inverts Hdd;
    EqDecSndEq;
    subst vvl; subst vvr; repnud Hta; allsimpl; cpx.
    rewrite DeqTrue in Hta;
    trivial; fail.



  (* back to the real business *)
  simpl.
  pose proof (Hyp _ t0) as Hd.
  unfold tAlphaEqG in Hd.
  rewrite DeqTrue in Hd.
  simpl in Hd.
  destruct Hd;[left; constructor; trivial | right; notAlpha].
  
- Case "pnode".
  destruct tb;[ right; notAlpha 
                | right; notAlpha 
                | right; notAlpha| ].

    introv Hal. inverts Hal.
    EqDecSndEq.
    GC. clear H6. clear X. clear H0.
    generalize dependent H3.
    remember (pnode p m) as xx.
    assert (isPNode xx) as Hxx by (subst;simpl; auto).
    clear Heqxx.
    generalize dependent xx.
    rewrite Hseqd0. 
    allsimpl.
    introv Hisv Heq.
    inverts Heq.
    cpx; fail.

    EqDec p p0;[| right].
    Focus 2. notAlpha.
    remember (pnode p m) as vvl.
    remember (pnode p0 m0) as vvr.
    assert (diffPProdsNode vvl vvr) as Hdd
     by (subst; unfold diffPProdsNode;
        cases_if; cpx).
    clear Heqvvr Heqvvl.
    remember (ppLhs G p).
    remember (ppLhs G p0).
    generalize dependent vvl.
    generalize dependent vvr.
    generalize Hseqd0.
    rewrite H0.
    introv. allsimpl.
    EqDecRefl. simpl.
    clear dependent p.
    introv Hta Hdd.
    clear H0 Hseqd1 Hseqd0 Heqp2 p1 m0 p0.
    inverts Hdd;
    EqDecSndEq;
    subst vvl; subst vvr; repnud Hta; allsimpl; cpx.
    rewrite DeqTrue in Hta;
    trivial; fail.

    (* back to the real business *)
  subst p0. unfold pAlphaEqG.
  rewrite DeqTrue.
  simpl. rename m0 into mb.
  destruct (Hyp mb [] []) as
  [Hleq | Hnleq];[left; constructor;auto | right; notAlpha].

- Case "mnil".
  dependent inversion mb. simpl. left.
  constructor.

  
- Case "mtcons".
  dependent inversion mb. simpl.
  subst. 
  remember (lhead lbva) as lha.
  remember (lhead lbvb) as lhb.
  remember (tail lbva) as lta.
  remember (tail lbvb) as ltb.
  clear Heqlha Heqlhb Heqlta Heqltb.
  specialize (Hyp0 m lta ltb).
  destruct (Hyp0); [| right ; notAlpha].
  destruct (decideAbsT vc ph Hyp h t lha lhb);
    [left; constructor; auto| right; notAlpha].
  
- Case "mpcons".
  dependent inversion mb. simpl.
  subst. 
  remember (lhead lbva) as lha.
  remember (lhead lbvb) as lhb.
  remember (tail lbva) as lta.
  remember (tail lbvb) as ltb.
  clear Heqlha Heqlhb Heqlta Heqltb.
  specialize (Hyp0 m lta ltb).
  destruct (Hyp0); [| right ; notAlpha].
  destruct (decideAbsP vc ph Hyp h p lha lhb);
    [left; constructor; auto| right; notAlpha].
Defined.
 
(*
Definition transpEm {G} {pl pr : EmbedProd G}
  (eqq : pl = pr)
  (tl : Term (gsymTN (epRhs G pl))) :=
(@transport _ _ _ (fun p => Term (gsymTN (epRhs G p)))  eqq tl).

Fixpoint tAlphaEqb {G} (vc : VarSym G) {gs : GSym G}
  (tl tr : Term gs) {struct tr}: bool :=
match (tl,tr) with
| (tnode pl ml, tnode pr mr) => true
| (tleaf tcl tl, tleaf tcr tr) 
    => Deq2Bool (deqSigTSemType) 
          (existT _ tcl tl) (existT _ tcr tr)
| (vleaf tcl tl, vleaf tcr tr) 
    => Deq2Bool (deqSigVType) 
          (existT _ tcl tl) (existT _ tcr tr)
| _ => false
end
with  pAlphaEqb {G} (vc : VarSym G) {gs : GSym G}
  (tl tr : Pattern gs) {struct tr} : bool :=
match (tl,tr) with
| (pnode pl ml, pnode pr mr) => true
| (ptleaf tcl tl, ptleaf tcr tr) 
    => Deq2Bool (deqSigTSemType) 
          (existT _ tcl tl) (existT _ tcr tr)
| (pvleaf tcl tl, pvleaf tcr tr) 
    => Deq2Bool (deqSigVType) 
          (existT _ tcl tl) (existT _ tcr tr)
| (embed pl tl, embed pr tr) =>
     match (deqEm G pl pr) with
     | right _ => false
     | left eqq => tAlphaEqb vc (transpEm eqq tl) tr
     end
| _ => false
end
with AlphaEqAbsb {G} (vc : VarSym G)
  (tl tr : Abstraction G vc) {struct tr}: bool :=
match (tl,tr) with
| (termAbs gsl lvl tll, termAbs gsr lvr trr) => 
    (beq_nat (length lvl) (length lvr)) &&
    match (deqGSym gsl gsr) with
    | right _ => false
    | left eqq => tAlphaEqb vc (transport eqq tll) trr
    end    
| (patAbs _ lvl tl, patAbs _ lvr tr) => true
|  _ => false
end.
  

*)
