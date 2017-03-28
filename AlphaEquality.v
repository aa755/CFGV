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
Require Export Swap.
Set Implicit Arguments.

Section GramVC.
Variable G : CFGV.
Variable vc  : VarSym G.

Notation vcDeq := (DeqVtype vc).

(* As will become evident
    later in [pAlphaEq], only the embeddings
    inside patterns get abstracted *)

(** CatchFileBetweenTagsAbsStart *)

Notation vcType := (vType vc).
Inductive Abstraction : Type :=
| termAbs: forall {gs : GSym G},
    list vcType -> Term gs -> Abstraction
| patAbs: forall {gs : GSym G},
    list vcType -> Pattern gs -> Abstraction.

(** CatchFileBetweenTagsAbsEnd *)


(** CatchFileBetweenTagsMakeAbsStart *)

Fixpoint MakeAbstractions {lgs} (m : Mixture lgs)
 (llB : list (list (vType vc))): list Abstraction :=
match m with
| mnil => []
| mtcons h tl=> (termAbs (lhead llB) h
                      ::(MakeAbstractions tl (tail llB)))
| mpcons h tl=> (patAbs (lhead llB) h
                      ::(MakeAbstractions tl (tail llB)))
end.

(** CatchFileBetweenTagsMakeAbsEnd *)


Definition MakeAbstractionsTNodeAux
    (lln: list (list nat))
    (mp : MixtureParam)
    (m :Mixture mp)
      : list Abstraction
:= MakeAbstractions m (lBoundVars vc lln m).

Definition MakeAbstractionsTNode (p: TermProd G)
    (m :Mixture (tpRhsAugIsPat p)) : list Abstraction
:= MakeAbstractionsTNodeAux (bndngPatIndices p) m.

(** there are no internal bindings within patterns *)
Definition MakeAbstractionsPNode
    {lgs: MixtureParam}
    (m: Mixture lgs)
     : list Abstraction
:= MakeAbstractions m [].


Definition swapAbs
           (a : Abstraction)
           (sw : Swapping vc)
    : Abstraction :=
match a with
| termAbs lbv t => termAbs (swapLVar sw lbv) (tSwap t sw)
| patAbs lbv t => patAbs (swapLVar sw lbv) (pSwap t sw)
end.

Definition swapLAbs
           (la : list Abstraction)
           (sw : Swapping vc)
    : list Abstraction :=
map (fun x => swapAbs x sw) la.

Lemma swapBndngVarsCommute:
(   forall (s : GSym G) (nt : Term s), True)
*
(   forall (s : GSym G) (pt : Pattern s) (sw : Swapping vc),
    swapLVar sw (pBndngVars vc pt) = pBndngVars  vc (pSwap pt sw)
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l)
    (sw : Swapping vc)
    (nn : nat),
    swapLVar sw (getBVarsNth vc m nn) = @getBVarsNth
                            _ vc _ (mSwap m sw) nn
).
Proof.
 GInduction; allsimpl; introns Hyp; intros; cpx; [ |  | | ].
- Case "pvleaf". rewrite DeqSym. symmetry.
  rewrite DeqSym. destruct_head_match;
  subst; auto.
- Case "pnode". simpl. simpl pBndngVars.
  rewrite mBndngVarsAsNth.
  rewrite mBndngVarsAsNth.
  autorewrite with fast.
  unfold swapLVar. unfold swapLVar in Hyp.
  rw map_flat_map.
  apply eq_flat_maps.
  intros nn Hin.
  unfold compose. trivial.
- simpl. destruct nn; auto.
- simpl. destruct nn; auto.
Qed.

Lemma  swapLBoundVarsCommute : forall
 (l : MixtureParam) (m : Mixture l)
 (sw: Swapping vc)
 (la: list (list nat)),
 (swapLLVar sw) (lBoundVars vc la m)
=
lBoundVars vc la
 (mSwap m sw).
Proof.
  intros. unfold lBoundVars.
  unfold swapLLVar, swapLVar.
  rw map_map.
  apply eq_maps.
  intros n Hin.
  unfold compose.
  rw map_flat_map.
  apply eq_flat_maps.
  intros nn Hinn.
  clear dependent n.
  clear dependent la.
  unfold compose.
  pose proof swapBndngVarsCommute as XX.
  unfold swapLVar in XX.
  exrepnd.
  cpx.
Qed.

Lemma MakeLAbsSwapCommute:
forall (mp : MixtureParam) (sw : Swapping vc) (m : Mixture mp)
  (lbv : list (list vcType)),
swapLAbs (MakeAbstractions m lbv) sw =
MakeAbstractions (mSwap m sw) (swapLLVar sw lbv).
  intros np sw m.
  induction m;  destruct lbv;
     allsimpl;auto;
  try(f_equal; auto; fail);[|];
  specialize (IHm []); allsimpl;
  f_equal; cpx.
Qed.

Lemma MakeAbsTNodeCommute: forall
    (p: TermProd G)
    (m :Mixture (tpRhsAugIsPat p))
    (sw: Swapping vc),
swapLAbs (MakeAbstractions m (lBoundVars vc (bndngPatIndices p) m)) sw =
MakeAbstractions (mSwap m sw)
  (lBoundVars vc (bndngPatIndices p) (mSwap m sw)).
Proof.
  intros.
  rw <- swapLBoundVarsCommute.
  apply MakeLAbsSwapCommute.
Qed.

Lemma MakeAbsPNodeCommute: forall
  (p: PatProd G)
  (m : Mixture (map (fun x : GSym G => (true, x)) (ppRhsSym p)))
  (sw: Swapping vc),
swapLAbs (MakeAbstractions m []) sw
   = MakeAbstractions (mSwap m sw) [].
Proof.
  intros. unfold MakeAbstractionsPNode.
  apply MakeLAbsSwapCommute.
Qed.

(* with the fixpoint, the strictness analyzer fails
Fixpoint pairWiseRelated {A B:Type}
  (R  : A -> B -> [univ])
  (la : list A) (lb : list B) : [univ] :=
match (la, lb)  with
| ([],[]) => unit
| (ha :: tla,hb :: tlb) =>
  (R ha hb) # (pairWiseRelated R tla tlb)
| (_,_) => void
end.
*)

(*
Inductive pairWiseRelated {A B:Type}
  (R  : A -> B -> [univ]) :
  list A -> list B -> [univ] :=
| pwNil : pairWiseRelated R [] []
| pwCons : forall (ha: A) (hb: B)
            (la: list A) (lb: list B),
            R ha hb
            -> pairWiseRelated R la lb
            -> pairWiseRelated R (ha::la) (hb::lb).
*)
(* unfortunately we cannot use the above because
    using it hides the inductive applications or R
    and the induction principle is weaker *)
(*  all patterns participate
  in making abstractions, possibly ones with empty lhs.
  prove property. that will make sure
  that they have same structure  *)

(* the embeddings need to alpha equal,
    shape should be exactly the same but variables can
    be different *)

(** CatchFileBetweenTagsAlphaStart *)

Notation zip := (combine).
Inductive tAlphaEq: forall {gs : (GSym G)},
      (Term gs) -> (Term gs) -> Type :=
| alt: forall T t, tAlphaEq (tleaf T t) (tleaf T t)
| alv: forall V v, tAlphaEq (vleaf V v) (vleaf V v)
| alnode: forall (p: TermProd G)
   (ma mb : Mixture (tpRhsAugIsPat p)),
   lAlphaEqAbs (MakeAbstractions ma (allBndngVars vc p ma))
               (MakeAbstractions mb (allBndngVars vc p mb))
   -> tAlphaEq (tnode p ma) (tnode p mb)

with pAlphaEq:
   forall {gs : (GSym G)},
      (Pattern gs) -> (Pattern gs) -> Type :=
| alpt: forall T t, pAlphaEq (ptleaf T t) (ptleaf T t)
| alpvar: forall vcc vara varb, pAlphaEq (pvleaf vcc vara)
                                         (pvleaf vcc varb)
| alembed: forall p nta ntb,
    tAlphaEq nta ntb -> pAlphaEq (embed p nta) (embed p ntb)
| alpnode:
    forall (p: PatProd G)
    (ma mb : Mixture (map (fun x => (true,x)) (ppRhsSym p))),
    lAlphaEqAbs  (MakeAbstractions ma [])
                 (MakeAbstractions mb [])
    -> pAlphaEq (pnode p ma) (pnode p mb)

with AlphaEqAbs: Abstraction -> Abstraction -> Type :=
| alAbT : forall {gs : GSym G}
    (lbva lbvb lbnew : list vcType)
    (tma tmb : Term gs),
    let swapa := zip lbva lbnew in
    let swapb := zip lbvb lbnew in
    length lbva = length lbnew
    -> length lbvb = length lbnew
    -> tFresh lbnew [tma,tmb]
    -> disjoint (lbva ++ lbvb) lbnew
    -> tAlphaEq (tSwap tma swapa) (tSwap tmb swapb)
    -> AlphaEqAbs (termAbs lbva tma) (termAbs lbvb tmb)
| alAbP : forall {gs : GSym G}
    (lbva lbvb lbnew : list vcType)
    (tma tmb : Pattern gs),
    let swapa := zip lbva lbnew in
    let swapb := zip lbvb lbnew in
    length lbva = length lbnew
    -> length lbvb = length lbnew
    -> pFresh lbnew [tma,tmb]
    -> disjoint (lbva ++ lbvb) lbnew
    -> pAlphaEq (pSwap tma swapa) (pSwap tmb swapb)
    -> AlphaEqAbs (patAbs lbva tma) (patAbs lbvb tmb)

with lAlphaEqAbs :
  list Abstraction -> list Abstraction -> Type :=
| lAlAbsNil : lAlphaEqAbs [] []
| lAlAbsCons : forall (ha hb: Abstraction)
            (la lb: list Abstraction),
            AlphaEqAbs ha hb
            -> lAlphaEqAbs la lb
            -> lAlphaEqAbs (ha::la) (hb::lb).

(** CatchFileBetweenTagsAlphaEnd *)

Scheme tAlphaEqMut := Minimality for tAlphaEq Sort Type
with pAlphaEqMut := Minimality for pAlphaEq Sort Type
with alphaEqAbsMut := Minimality for AlphaEqAbs Sort Type
with lAlphaEqAbsMut := Minimality for lAlphaEqAbs Sort Type.

(** again, just renaming variables to more intuitive ones
  and putting all 4 parts in 1 lemma, so
  that the user gets all 4 proofs in 1 shot.
  Usually even to prove, the other onese have to
  be proved anyways *)
Lemma GAlphaInd:
forall (P : forall gs : GSym G, Term gs -> Term gs -> [univ])
         (PP : forall gs : GSym G, Pattern gs -> Pattern gs -> [univ])
         (PA : Abstraction -> Abstraction -> [univ])
         (PLA : list Abstraction -> list Abstraction -> [univ]),
       (forall (T : Terminal G) (t : tSemType G T),
        P (gsymT T) (tleaf T t) (tleaf T t)) ->
       (forall (V : VarSym G) (v : vType V),
        P (gsymTN (vSubstType G V)) (vleaf V v) (vleaf V v)) ->
       (forall (p : TermProd G) (ma mb : Mixture (tpRhsAugIsPat p)),
        lAlphaEqAbs (MakeAbstractions ma (allBndngVars vc p ma))
              (MakeAbstractions mb (allBndngVars vc p mb)) ->
        PLA (MakeAbstractions ma (allBndngVars vc p ma))
            (MakeAbstractions mb (allBndngVars vc p mb)) ->
        P (gsymTN (tpLhs G p)) (tnode p ma) (tnode p mb)) ->
       (forall (T : Terminal G) (t : tSemType G T),
        PP (gsymT T) (ptleaf T t) (ptleaf T t)) ->
       (forall (vcc : VarSym G) (vara varb : vType vcc),
        PP (gsymV vcc) (pvleaf vcc vara) (pvleaf vcc varb)) ->
       (forall (p : EmbedProd G) (nta ntb : Term (gsymTN (epRhs G p))),
        tAlphaEq nta ntb ->
        P (gsymTN (epRhs G p)) nta ntb ->
        PP (gsymPN (epLhs G p)) (embed p nta) (embed p ntb)) ->
       (forall (p : PatProd G)
          (ma mb : Mixture (map (fun x : GSym G => (true, x)) (ppRhsSym p))),
        lAlphaEqAbs (MakeAbstractions ma []) (MakeAbstractions mb []) ->
        PLA (MakeAbstractions ma []) (MakeAbstractions mb []) ->
        PP (gsymPN (ppLhs G p)) (pnode p ma) (pnode p mb)) ->
       (forall (gs : GSym G) (lbva lbvb lbnew : list vcType)
          (tma tmb : Term gs),
        let swapa := combine lbva lbnew in
        let swapb := combine lbvb lbnew in
        length lbva = length lbnew ->
        length lbvb = length lbnew ->
        tFresh lbnew [tma, tmb] ->
        disjoint (lbva ++ lbvb) lbnew ->
        tAlphaEq (tSwap tma swapa) (tSwap tmb swapb) ->
        P gs (tSwap tma swapa) (tSwap tmb swapb) ->
        PA (termAbs lbva tma) (termAbs lbvb tmb)) ->
       (forall (gs : GSym G) (lbva lbvb lbnew : list vcType)
          (tma tmb : Pattern gs),
        let swapa := combine lbva lbnew in
        let swapb := combine lbvb lbnew in
        length lbva = length lbnew ->
        length lbvb = length lbnew ->
        pFresh lbnew [tma, tmb] ->
        disjoint (lbva ++ lbvb) lbnew ->
        pAlphaEq (pSwap tma swapa) (pSwap tmb swapb) ->
        PP gs (pSwap tma swapa) (pSwap tmb swapb) ->
        PA (patAbs lbva tma) (patAbs lbvb tmb)) ->
       PLA [] [] ->
       (forall (ha hb : Abstraction) (la lb : list Abstraction),
        AlphaEqAbs ha hb ->
        PA ha hb -> lAlphaEqAbs la lb -> PLA la lb -> PLA (ha :: la) (hb :: lb))
        ->
((forall (gs : GSym G) (ta tb : Term gs), tAlphaEq ta tb -> P gs ta tb)
 *(forall (gs : GSym G) (pa pb : Pattern gs),
      pAlphaEq pa pb -> PP gs pa pb)
 *(forall aa ab : Abstraction, AlphaEqAbs aa ab -> PA aa ab)
 *(forall la lb : list Abstraction, lAlphaEqAbs la lb -> PLA la lb)
).
Proof.
intros. dands.
- eapply tAlphaEqMut; eauto.
- eapply pAlphaEqMut; eauto.
- eapply alphaEqAbsMut; eauto.
- eapply lAlphaEqAbsMut; eauto.
Defined.


Definition mAlphaEq
   {mp : MixtureParam}
   (ma mb : Mixture mp)
   (lln : list (list nat)) :=
lAlphaEqAbs
  (MakeAbstractionsTNodeAux lln ma)
  (MakeAbstractionsTNodeAux lln mb).

End GramVC.


Ltac GAlphaInd :=
  apply GAlphaInd ; [
                        Case "tleaf"
                      | Case "vleaf"
                      | Case "tnode"
                      | Case "ptleaf"
                      | Case "pvleaf"
                      | Case "pembed"
                      | Case "pnode"
                      | Case "termAbs"
                      | Case "patAbs"
                      | Case "laNil"
                      | Case "laCons"
].

Definition tAlphaEqual {G : CFGV} {gs : GSym G} (ta tb : Term gs):=
forall (vc: VarSym G), tAlphaEq vc ta tb.

(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)

(*
Inductive tAlphaEq: forall {gs : (GSym G)},
      (Term gs) -> (Term gs) -> [univ] :=
| alt: forall T t, tAlphaEq (tleaf T t) (tleaf T t)
| alv: forall V v, tAlphaEq (vleaf V v) (vleaf V v)
| alnode: forall (p: TermProd G)
    (ma mb :Mixture (tpRhsAugIsPat p)),
   lAlphaEqAbs (MakeAbstractions ma (allBndngVars vc p ma))
               (MakeAbstractions mb (allBndngVars vc p mb))
   -> tAlphaEq (tnode p ma) (tnode p mb)
with pAlphaEq: forall {gs : (GSym G)},
      (Pattern gs) -> (Pattern gs) -> [univ] :=
| alpt: forall T t, pAlphaEq (ptleaf T t) (ptleaf T t)
| alpvar: forall V va vb, pAlphaEq (pvleaf V va) (pvleaf V vb)
| alembed: forall p nta ntb,
    tAlphaEq nta ntb ->  pAlphaEq (embed p nta) (embed p ntb)
| alpnode: forall (p: PatProd G)
    (ma mb : Mixture (map (fun x => (true,x)) (ppRhsSym p))),
    lAlphaEqAbs  (MakeAbstractions ma [])
                 (MakeAbstractions mb [])
    -> pAlphaEq (pnode p ma) (pnode p mb)
with AlphaEqAbs : Abstraction -> Abstraction -> [univ] :=
| alAbT : forall {gs : GSym G} (lbva lbvb lbnew : list vcType)
    (tma tmb : Term gs),
    let swapa := combine lbva  lbnew in
    let swapb := combine lbvb  lbnew in
    length lbva = length lbnew
    -> length lbvb = length lbnew
    -> tFresh lbnew [tma,tmb]
    -> disjoint (lbva ++ lbvb) lbnew
    -> tAlphaEq (tSwap tma swapa) (tSwap tmb swapb)
    -> AlphaEqAbs (termAbs lbva tma) (termAbs lbvb tmb)
| alAbP : forall {gs : GSym G} (lbva lbvb lbnew : list vcType)
    (tma tmb : Pattern gs),
    let swapa := combine lbva  lbnew in
    let swapb := combine lbvb  lbnew in
    length lbva = length lbnew
    -> length lbvb = length lbnew
    -> pFresh lbnew [tma,tmb]
    -> disjoint (lbva ++ lbvb) lbnew
    -> pAlphaEq (pSwap tma swapa) (pSwap tmb swapb)
    -> AlphaEqAbs (patAbs lbva tma) (patAbs lbvb tmb)
with lAlphaEqAbs:
      list Abstraction -> list Abstraction -> [univ] :=
| lAlAbsNil : lAlphaEqAbs [] []
| lAlAbsCons : forall (ha hb: Abstraction)
    (la lb: list Abstraction), AlphaEqAbs ha hb
    -> lAlphaEqAbs la lb  -> lAlphaEqAbs (ha::la) (hb::lb).
*)
