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
Require Export GVariables.
Set Implicit Arguments.

(** printing #  $\times$ #×# *)
(** printing &  $\times$ #×# *)




(** used in [bindingInfoCorrect] below.
   Also, see [ValidIndicesDecidable] below*)
Definition ValidIndices {A B : Type}
  (bindingInfo : list (nat * nat))
  (rhsSyms : list (A + B)) : [univ] 
:= (
      forall n m, 
      LIn (n,m) bindingInfo
      -> (m < length rhsSyms) # (n < length rhsSyms)
          # (true = liftNth isInl rhsSyms n)
   )
   #
   (
      forall n, 
        (true = liftNth isInl rhsSyms n)
        -> LIn n (map (@fst _ _) bindingInfo)
   )
    #no_repeats bindingInfo.

(** For concretely specified grammars,
  one can just compute the following lemma to get the
  proof of [ValidIndices]. See the tactic (Ltac)
  [proveBindingInfoCorrect] below. *)
Lemma ValidIndicesDecidable:
  forall {A B : Type}
  (bindingInfo : list (nat * nat))
  (rhsSyms : list (A + B)),
  decidable (ValidIndices bindingInfo rhsSyms).
Proof.
  intros.
  unfold ValidIndices.
  apply decidable_prod;[|apply decidable_prod].
  - induction bindingInfo as [| (n,m) bindingInfo Hind];
      [left; dands |]; cpx.
    dorn Hind;[| right]; cpx.
    remember (liftNth isInl rhsSyms n) as bl.
    destruct (lt_dec m (length rhsSyms));
    destruct (lt_dec n (length rhsSyms));
    destruct bl; try rewrite <- Heqbl;
    try(left; introv Hin; repeat(in_reasoning); cpx; fail);
    [| | | | | | ];
    right; introv Hin;
    specialize (Hin _ _ (inl eq_refl));
    try rewrite <- Heqbl in Hin;
    dands; cpx.

  - remember ((map (fst (B:=nat)) bindingInfo)) as bif.
    clear dependent bindingInfo.
    revert bif. unfold liftNth;
    induction rhsSyms as [| rs rhsSyms Hind];
      [left; intro n; destruct n;
         simpl; cpx |].
    intro bifCons.
    remember (flat_map 
      (fun n=> match n with
               |0 => []
               | S m => [m] end) bifCons)
      as bif.
    specialize (Hind bif).
    dorn Hind; [| right]; cpx.
    + destruct rs as [sa| sb];[|left; destruct n;
            allsimpl; cpx].
      * destruct (in_deq _ deq_nat 0 bifCons); cpx;
        [left; destruct n | right]; simpl;
        subst bif; cpx;[].
        
        introv Heq.
        apply Hind in Heq.
        apply lin_flat_map in Heq.
        exrepnd.
        destruct x; cpx.
        inverts Heq0; cpx; fail.

      * introv Heq. subst bif.
        specialize (Hind ( n)).
        apply Hind in Heq. clear Hind.
        apply lin_flat_map in Heq.
        exrepnd. destruct x; cpx.
        inverts Heq0; cpx.
    + introv Hc. apply Hind. clear Hind. introv Heq.
      subst bif. apply lin_flat_map.
      specialize (Hc (S n)). simpl in Hc.
      apply Hc in Heq.
      exists (S n). dands; cpx.

  - apply no_repeat_dec. apply deq_prod; exact deq_nat.
Defined.



  
(* using some ideas from 
  http://gallium.inria.fr/~xleroy/publi/validated-parser.pdf

  Coq sources are linked in sources in [9].

  specifically, cparser/validator/Grammar.v

*)

(** CatchFileBetweenTagsCFGVStart *)
Record CFGV := {
  Terminal : Type;   VarSym : Type; 
  TNonTerminal : Type;   PNonTerminal : Type;

  PatProd : Type;  EmbedProd : Type;  TermProd : Type;

  varSem : VarSym -> VarType;
  vSubstType : VarSym -> TNonTerminal;
  tSemType : Terminal -> Type;

  ppLhsRhs: PatProd -> 
    (PNonTerminal * list (PNonTerminal 
                           + (Terminal + VarSym)));

  epLhsRhs : EmbedProd -> (PNonTerminal * TNonTerminal);
  
  tpLhsRhs: TermProd -> 
    (TNonTerminal * list ((PNonTerminal + VarSym)
                          +(Terminal+TNonTerminal)));
  
  bindingInfo : TermProd -> list (nat * nat);
  bindingInfoCorrect: forall (p: TermProd),
      ValidIndices (bindingInfo p) (snd (tpLhsRhs p));
(** }. CatchFileBetweenTagsCFGVEnd *)

  DeqVarSym : Deq VarSym;
  deqT : Deq Terminal;
  deqNT : Deq TNonTerminal;
  deqPT : Deq PNonTerminal;
  deqPr : Deq TermProd;
  deqEm : Deq EmbedProd;
  deqPPr : Deq PatProd;
  deqTSem : forall (t: Terminal), Deq (tSemType t)

}.


Definition vType {G: CFGV} (vc : VarSym G) : Type :=
  (typ (varSem G vc)).

(** A more intuitive way to denote symbols of a CFGV :
    instead of inl inr.... *)

(** CatchFileBetweenTagsGSymStart *)
Inductive GSym (G: CFGV) : Type :=
| gsymT : Terminal G -> GSym G
| gsymV : VarSym G -> GSym G
| gsymTN : TNonTerminal G -> GSym G
| gsymPN : PNonTerminal G -> GSym G.
(** CatchFileBetweenTagsGSymEnd *)

(** Make the [CFGV] argument implicit *) 
Arguments gsymT {G} _.
Arguments gsymV {G} _.
Arguments gsymTN {G} _.
Arguments gsymPN {G} _.

Arguments bindingInfo {c} _.

Lemma deqGSym :  forall (G: CFGV),
  Deq (GSym G).
Proof.
intros.
intros sa sb.
destruct sa as [sa|sa|sa|sa]; destruct sb as [sb|sb|sb|sb]; 
try (right; introv Hc; inverts Hc; cpx; fail).
- destruct (deqT G sa sb);[left; subst|right; introv HC; inverts HC]; cpx.
- destruct (DeqVarSym G sa sb);[left; subst|right; introv HC; inverts HC]; cpx.
- destruct (deqNT G sa sb);[left; subst|right; introv HC; inverts HC]; cpx.
- destruct (deqPT G sa sb);[left; subst|right; introv HC; inverts HC]; cpx.
Defined.


Hint Resolve deqT deqTSem DeqVarSym deqNT deqPT deqGSym deqPr deqEm deqPPr: Deq.



Definition  prhs_aux {G : CFGV} 
  (symSum :((PNonTerminal G + VarSym G) 
              +(Terminal G + TNonTerminal G))) : (GSym G) :=
match symSum with
| inl (inl p) => gsymPN p
| inl (inr vc) => gsymV vc
| inr (inl t) => gsymT t
| inr (inr nt) => gsymTN nt
end.

Definition tpRhsSym {G: CFGV} (p:TermProd G) : list (GSym G)
:=map (prhs_aux) (snd (tpLhsRhs G p)).

Definition  ptrhs_aux {G : CFGV} 
  (symSum :((PNonTerminal G)+ (Terminal G + VarSym G))) 
      : (GSym G) :=
match symSum with
| (inl p) => gsymPN p
| inr (inl t) => gsymT t
| inr (inr v) => gsymV v
end.

Definition gsymNotNT {G : CFGV} (s : GSym G) :=
match s with
| gsymT _ => True
| gsymV _ => True
| gsymTN _ => False
| gsymPN _ => True
end.

Lemma ptrhs_aux_nonNT : forall {G: CFGV} 
    (symSum :((PNonTerminal G)+ (Terminal G + VarSym G))) ,
  gsymNotNT (ptrhs_aux symSum).
Proof.
  intros.
  dorn symSum;[|dorn symSum]; simpl; auto.
Qed.

Definition ppRhsSym {G: CFGV} (p:PatProd G) : list (GSym G)
:=map (ptrhs_aux) (snd (ppLhsRhs G p)).

Definition tpLhs (G: CFGV) (p:TermProd G) : TNonTerminal G
:= (fst (tpLhsRhs G p)).

Definition epLhs (G: CFGV) (p:EmbedProd G) : PNonTerminal G
:= (fst (epLhsRhs G p)).

Definition epRhs (G: CFGV) (p:EmbedProd G) : TNonTerminal G
:= (snd (epLhsRhs G p)).

Definition ppLhs (G: CFGV) (p:PatProd G) : PNonTerminal G
:= (fst (ppLhsRhs G p)).

Definition gsymNotP {G : CFGV} (s : GSym G) :=
match s with
| gsymT _ => True
| gsymV _ => True
| gsymTN _ => True
| gsymPN _ => False
end.


Arguments DeqVarSym {c}  _ _.


Definition flatten {A : Type} (l : list (list A)) : list A:= 
  flat_map (fun x => x) l.


(* how many times the nth symbol in rhs of production p is bound.
    (not the most efficient algorithm) *)
Definition bindCount {G : CFGV} (p: TermProd G) (n : nat) :=
  let lnat := (map (@fst _ _) (bindingInfo p))
    in count_occ deq_nat lnat n.

(* the following can be written better using [LIn]
Definition isBound {G : CFGV} (p: TermProd G) (n : nat) :=
  negb (beq_nat (bindCount p n) 0).
*)


(* Now we (parially) 
    define the semantics of the language,
    It is essentially a parse tree.
    The full semantics also needs
    to formalize variable binding semantics;
    e.g. alpha equality and substitution.
    
    The parse tree s parametrized by the
    head symbol.
 *)


Definition prhsIsBound {G : CFGV} (p: TermProd G) : list bool := 
 (map isInl (snd (tpLhsRhs G p))).

Definition MixtureParam {G : CFGV} :=
  list (bool * (GSym G)).

Definition MParamCorrectb {G : CFGV} (pp: @MixtureParam G)
   : bool :=
forallb  (fun p=> match p with 
                   | (false, gsymPN _) => false
                   | _ => true
                   end) 
          pp.


(* augment rhs with indicators whether a pattern is bound somewhere*)
Definition tpRhsAugIsPat {G : CFGV} (p: TermProd G) 
    : MixtureParam := 
 combine (prhsIsBound p) (tpRhsSym p).



(* TODO: Show some examples. encode Coq in the standard inductive
    way and then use this CFGV. Prove bijection.
    Ignore bindings to begin with.
*)


Definition bindingSourcesNth {G:CFGV} 
  (p: TermProd G) (k:nat) : list nat :=
flat_map 
     (fun pp : (nat * nat) 
                => let (n,m) := pp in 
                    if (beq_nat k m) then [n] else [])
     (bindingInfo p).

Definition ValidNthSrc (len : nat) (ln: list nat):=
  no_repeats ln
  # lForall (fun n =>  n < len) ln.


Lemma bsNthValid : forall {G:CFGV}
(p: TermProd G) (k:nat),
ValidNthSrc (length (tpRhsSym p)) (bindingSourcesNth p k).
Proof.
  intros. unfold ValidNthSrc.
  unfold bindingSourcesNth, bindingInfo, tpRhsSym.
  autorewrite with fast.
  pose proof (bindingInfoCorrect G p) as XX.
  destruct (tpLhsRhs G p) as [lhs ls].
  destruct G; allsimpl; cpx.

  allsimpl. remember ((bindingInfo0 p)) as bi. clear Heqbi.
  allsimpl. clear  bindingInfoCorrect0.
  repnud XX. clear XX1.
  induction bi; dands; allsimpl;  cpx;
  allrw no_repeats_cons;
  exrepnd;

  apply IHbi in XX1; exrepnd; cpx;
  remember (beq_nat k a) as bn; destruct bn; cpx;
  allrw no_repeats_cons; allsimpl; dands;  cpx.
  - introv Hin. rw lin_flat_map in Hin.
    exrepnd.
    remember (beq_nat k x) as bkx; destruct bkx; allsimpl; cpx.
    dorn Hin0; subst; cpx.
    allapply beq_nat_eq.
    subst. subst. cpx.
  - pose proof (XX0 _ _ (inl eq_refl)).
    repnd; cpx.
Qed.

Definition bndngPatIndices {G:CFGV} 
  (p: TermProd G) : list  (list nat) :=
map (bindingSourcesNth p) (seq 0 (length (tpRhsSym p))).

Definition validBsl (len:nat) (lln: list (list nat)) :=
lforall (ValidNthSrc len) lln.

Lemma  bndngPatIndicesValid : forall
{G:CFGV} (p: TermProd G),
validBsl (length (tpRhsSym p)) (bndngPatIndices p).
Proof.
  intros.
  unfolds_base.
  unfold bndngPatIndices.
  introv Hin.
  apply in_map_iff in Hin.
  exrepnd.
  subst.
  apply bsNthValid.
Qed.

Lemma  bndngPatIndicesValid2 : forall
{G:CFGV} (p: TermProd G),
validBsl (length (snd (tpLhsRhs G p))) (bndngPatIndices p).
Proof.
  intros.
  pose proof (bndngPatIndicesValid p) as X.
  unfold tpRhsSym in X.
  autorewrite with fast in X.
  trivial.
Qed.

Lemma DeqVtype : forall  {G:CFGV} (vc : VarSym G),
     Deq (vType vc).
Proof.
  intros. unfold vType.
  match goal with
  [ |- Deq (typ ?xx)] => destruct xx as [? vd]
  end.
  repnud vd. auto.
Defined.

Hint Resolve DeqVtype : Deq.

Definition vFreshVar 
  {G : CFGV} 
  {vc : VarSym G}
  (lvAvoid: list (vType vc))
  (v: (vType vc)) : vType vc :=
  ((fresh (varSem G vc)) lvAvoid [v]).

Definition GFreshVars 
  {G : CFGV} 
  {vc : VarSym G}
  (lvAvoid: list (vType vc))
  (lv: list (vType vc)) : list (vType vc)  :=
  (FreshDistinctVars (varSem G vc) lv lvAvoid).

Lemma FreshDistVarsSpec: forall
  {G : CFGV} {vc : VarSym G}
  (lvAvoid: list (vType vc))
  (lv: list (vType vc)),
  let lvn := (GFreshVars  lvAvoid lv) in
  no_repeats lvn # disjoint lvn lvAvoid # length lvn= length lv.
Proof.
  intros.
  subst lvn.
  unfold GFreshVars.
  pose proof( 
    FreshDistVarsSpec  lv lvAvoid).
  allsimpl.
  exrepnd; dands; cpx.
Qed.


Lemma vFreshVarSpec : forall 
  {G : CFGV} 
  {vc : VarSym G}
  (lvAvoid: list (vType vc))
  (v: (vType vc)),
  ! LIn (vFreshVar lvAvoid v) lvAvoid.
Proof.
  intros.
  unfold vFreshVar.
  revert v. revert lvAvoid.
  unfold vType.
  destruct  (varSem G vc) as [T vd Vf Vfc].
  allsimpl.
  exrepnd. allsimpl.
  cpx.
Qed.

(** also guaranteed to be different from the input *)
Definition vFreshDiff
  {G : CFGV} 
  {vc : VarSym G}
  (lvAvoid: list (vType vc))
  (v: (vType vc)) :=
  (fresh (varSem G vc)) (v::lvAvoid) [v].

Lemma vFreshDiffSpec : forall 
  {G : CFGV} 
  {vc : VarSym G}
  (lvAvoid: list (vType vc))
  (v: (vType vc)),
  ! LIn (vFreshDiff (lvAvoid) v) (v::lvAvoid).
Proof.
  intros.
  apply vFreshVarSpec.
Qed.

Lemma length_pRhsAugIsPat : forall {G : CFGV}  (p : TermProd G),
  length (tpRhsAugIsPat p) = length ((snd (tpLhsRhs G p))).
Proof.
  intros. simpl.
  unfold tpRhsAugIsPat, prhsIsBound , tpRhsSym.
  rewrite combine_length.
  autorewrite with fast.
  rewrite min_eq; refl.
Qed.

Lemma GFreshDistRenWSpec: forall
   {G:CFGV} (vc : VarSym G)
  (lv :list (vType vc))
  (lvAvoid :list (vType vc)),
  {lvn : list (vType vc) $
  no_repeats lvn # disjoint lvn lvAvoid 
  # length lvn= length lv}.
Proof.
  intros. eapply FreshDistRenWSpec; eauto.
Defined.

Lemma deqMixP : forall {G}, Deq (@MixtureParam G).
Proof.
  unfold MixtureParam.
  eauto with Deq.
Defined.

Lemma deqSigVType : 
  forall {G}, (Deq (sigT (@vType G))).
Proof.
  intros.
  apply sigTDeq;
  eauto with Deq.
Defined.

Lemma deqSigTSemType : 
  forall {G}, (Deq (sigT (tSemType G))).
Proof.
  intros.
  apply sigTDeq;
  eauto with Deq.
Defined.


Definition decDisjointV {G} (vc : VarSym G)
   (la lb : list (vType vc)) :
    (disjoint la lb[+]!disjoint la lb)
  := dec_disjoint (DeqVtype vc) la lb.

Ltac proveBindingInfoCorrect :=
  let p:= fresh "tprod" in
  let d:= fresh "decVal" in
  let Heqd:= fresh "Heq" d in
  intro p;
  match goal with
  [ |- ValidIndices ?binf ?rhsSyms ] =>
    remember (ValidIndicesDecidable binf rhsSyms) as d eqn:Heqd;
      destruct p; unfold ValidIndicesDecidable in Heqd; allsimpl;
      destruct d; auto; inverts Heqd
  end.

Ltac proveDeqInductiveNonrec :=
  let x:= fresh "xdl" in
  let y:= fresh "axr" in
  let Hc:= fresh "Hcontra" in
  intros x y ; destruct x; destruct y; 
    try (left; cpx; fail); (try right; introv Hc; inverts Hc ; cpx).
(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)

(*
Definition vFreshDistRenLL 
  {G : CFGV} (vc : VarSym G):=
  FreshDistinctRenListList (snd (projT2 (vSemType G vc))).
*)

(* Lemma  : forall {G : CFGV},
  Deq (VarSym G).
Proof.
  intros.
  destruct G.
  simpl.
  (* info_eauto with Deq. *)
    apply Finite_Deq.
    exact FinV0.
Defined. *)

(*
with Patterns {G : CFGV} :
  list (GSym G) -> Type :=
| pnil : Patterns []
| pcons : forall  {h: GSym G}
        {tl: list (GSym G) }
        (ph: Pattern h )
        (ptl: Patterns tl),
          Patterns (h::tl)
*)
(* not necessary till we do parsing.
  these implied decidability of equality.
  We added those to make
  depedent destruction to work.

  FinV: Finite VarSym;
  FinPt: Finite PNonTerminal;
  FinT: Finite Terminal;
  FinPr: Finite TermProd;
  FinEmb: Finite EmbedProd;
  FinNT: Finite TNonTerminal;
  FinPat: Finite PatProd;
*)
(* The following legitimate definition is
    rejected by Coq's too strict strict-positivity checker.
[[
Require Import Tuples.
Inductive ParseTree (G : CFGV) : (GSymb G) -> Type :=
| leaf : forall (t :Token G), ParseTree G (Token2Gsymb t)
| tnode : forall (p: TermProd G),
    tuple (map (ParseTree G) (prhs G p))
    -> (ParseTree G  (gsymTN _ _ _ (tpLhs G p))).
]]
*)
