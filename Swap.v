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
Require Import AssociationList.
Set Implicit Arguments.

Definition oneSwapVar
           {G  : CFGV}
           {vc : VarSym G}
           (v  : vType vc)
           (oneSwapping : vType vc * vType vc)
: vType vc :=
  let (a,b) := oneSwapping in
  if DeqVtype vc v a
  then b
  else if DeqVtype vc v b
       then a
       else v.

(** CatchFileBetweenTagsSwapVarStart *)

Definition Swapping {G} (vc  : VarSym G)
:= list (vType vc * vType vc).

Definition swapVar {G} {vc : VarSym G} 
  (sw : Swapping vc) (v : vType vc) : vType vc 
:= fold_left oneSwapVar sw v .

(** CatchFileBetweenTagsSwapVarEnd *)

(** One could define the above as
    [fold_right] to *)


Fixpoint tSwap
         {G  : CFGV}
         {vc : VarSym G}
         (gs : (GSym G))
         (pt : Term gs)
         (sub : Swapping vc) {struct pt} : Term gs :=
  match pt in Term gs return Term gs with
    | tleaf a b => tleaf a b
    | vleaf vcc var =>
      vleaf vcc (match DeqVarSym vc vcc with
                   | left eqq => swapVar (transport eqq sub) var
                   | right _ => var
                 end)
    | tnode p mix => tnode p (mSwap mix sub)
  end
with pSwap
       {G  : CFGV}
       {vc : VarSym G}
       {gs : GSym G}
       (pt : Pattern gs)
       (sub : Swapping vc) {struct pt} : Pattern gs  :=
  match pt with
    | ptleaf a v => ptleaf a v
    | pvleaf vcc var =>
      pvleaf vcc (match DeqVarSym vc vcc with
                    | left eqq => swapVar (transport eqq sub) var
                    | right _ => var
                  end)
    | pnode p lpt => pnode p (mSwap lpt sub)
    | embed p nt => embed p (tSwap nt sub)
  end
with mSwap
       {G  : CFGV}
       {vc : VarSym G}
       (lgs : list (bool * GSym G))
       (pts : Mixture lgs)
       (sub : Swapping vc)
       {struct pts}
     : Mixture lgs  :=
  match pts in Mixture lgs return Mixture lgs with
    | mnil  => mnil
    | mtcons _ _ ph ptl =>
      mtcons (tSwap ph sub) (mSwap ptl sub)
    | mpcons _ _ ph ptl =>
      mpcons (pSwap ph sub) (mSwap ptl  sub)
  end.


(** These definitions of freshness are perhaps too much on the
  safe side. However, since we have an infinite supply of fresh
  variables, there is not much concern *)
Definition pFresh
           {G  : CFGV}
           {vc : VarSym G}
           {sym : GSym G}
           (hlnew : list (vType vc))
           (pts : list (Pattern sym)) :=
  disjoint hlnew (flat_map pAllVars pts)
  # no_repeats hlnew.

Definition tFresh
           {G  : CFGV}
           {vc : VarSym G}
           {sym : GSym G}
           (hlnew : list (vType vc))
           (ts : list (Term sym)):=
  disjoint hlnew (flat_map tAllVars ts)
  # no_repeats hlnew.

Definition mFresh
           {G  : CFGV}
           {vc : VarSym G}
           {lgs : list (bool * GSym G)}
           (hlnew : list (vType vc))
           (ms : list (Mixture lgs)):=
  disjoint hlnew (flat_map mAllVars ms)
  # no_repeats hlnew.

Lemma tFreshSubset : forall 
           {G  : CFGV}
           {vc : VarSym G}
           {sym : GSym G}
           (hlnew : list (vType vc))
           (tsa tsb : list (Term sym)),
tFresh hlnew tsa 
-> subset tsb tsa 
-> tFresh hlnew tsb.
Proof.
  introns XX. unfold tFresh.
  unfold tFresh in XX. repnd;
  dands; [ SetReasoning | trivial].
Qed.

Lemma pFreshSubset : forall 
           {G  : CFGV}
           {vc : VarSym G}
           {sym : GSym G}
           (hlnew : list (vType vc))
           (tsa tsb : list (Pattern sym)),
pFresh hlnew tsa 
-> subset tsb tsa 
-> pFresh hlnew tsb.
Proof.
  introns XX. unfold pFresh.
  unfold pFresh in XX. repnd;
  dands; [ SetReasoning | trivial].
Qed.
   
Hint Resolve pFreshSubset tFreshSubset : SetReasoning.

Definition EquiVariantRel {G : CFGV} {vc : VarSym G}
  {TA :Type} 
  {TB :Type}
  (swapA : TA -> Swapping vc -> TA)
  (swapB : TB -> Swapping vc -> TB)
  (R : TA -> TB -> [univ]) :=
  forall (ta : TA) (tb: TB),
  R ta tb 
  -> forall (sw : Swapping vc), R (swapA ta sw) (swapB tb sw).
  
Definition EquiVariantRelSame {G : CFGV} {vc : VarSym G}
  {TA :Type} 
  (swapA : TA -> Swapping vc -> TA)
  (R : TA -> TA -> [univ]) :=
  EquiVariantRel swapA swapA R.

Definition EquiVariantRelUn {G : CFGV} {vc : VarSym G}
  {TA :Type} 
  (swapA : TA -> Swapping vc -> TA)
  (R : TA -> [univ]) :=
  forall (ta : TA),
  R ta
  -> forall (sw : Swapping vc), R (swapA ta sw).

Definition EquiVariantFn {G : CFGV} {vc : VarSym G}
  {TA :Type} 
  {TB :Type}
  (swapA : TA -> Swapping vc -> TA)
  (swapB : TB -> Swapping vc -> TB)
  (f : TA -> TB ) :=
  forall (ta : TA) (sw : Swapping vc),
  swapB (f ta) sw = f (swapA ta sw).

Definition EquiVariantFn2 {G : CFGV} {vc : VarSym G}
  {TA :Type} 
  {TB :Type}
  {TC :Type}
  (swapA : TA -> Swapping vc -> TA)
  (swapB : TB -> Swapping vc -> TB)
  (swapC : TC -> Swapping vc -> TC)
  (f : TA -> TB -> TC) :=
  forall (ta : TA) (tb : TB) (sw : Swapping vc),
  swapC (f ta tb) sw = f (swapA ta sw) (swapB tb sw).

Definition EquiVariantFn3 {G : CFGV} {vc : VarSym G}
  {TA :Type} 
  {TB :Type}
  {TC :Type}
  {TD :Type}
  (swapA : TA -> Swapping vc -> TA)
  (swapB : TB -> Swapping vc -> TB)
  (swapC : TC -> Swapping vc -> TC)
  (swapD : TD -> Swapping vc -> TD)
  (f : TA -> TB -> TC -> TD) :=
  forall (ta : TA) (tb : TB) (tc : TC) (sw : Swapping vc),
  swapD (f ta tb tc) sw = f (swapA ta sw) (swapB tb sw) (swapC tc sw).

Definition swapLVar
           {G  : CFGV}
           {vc :  VarSym G}
           (sw : Swapping vc)
           (lv : list (vType vc)) : list (vType vc) :=
  map (swapVar sw) lv.

Definition swapLLVar 
           {G  : CFGV}
           {vc :  VarSym G}
           (s : Swapping vc)
           (vs : list (list (vType vc))) :=
  map (swapLVar s) vs.

Definition swapSwap
           {G  : CFGV}
           {vc :  VarSym G}
           (sw al: Swapping vc) : Swapping vc :=
  map (fun x => (swapVar sw (fst x),swapVar sw (snd x))) al.

Fixpoint pSwapEmbed
       {G  : CFGV}
       {vc : VarSym G}
       {gs : GSym G}
       (pt : Pattern gs)
       (swEmbed  : Swapping vc) {struct pt} : Pattern gs  :=
  match pt with
    | ptleaf a v => ptleaf a v
    | pvleaf vcc var => pvleaf vcc var
    | pnode p lpt => pnode p (mSwapEmbed lpt swEmbed)
    | embed p nt => embed p (tSwap nt swEmbed)
  end
with mSwapEmbed
       {G  : CFGV}
       {vc : VarSym G}
       {lgs : list (bool * GSym G)}
       (pts : Mixture lgs)
       (swEmbed : Swapping vc)
       {struct pts}
     : Mixture lgs  :=
  match pts in Mixture lgs return Mixture lgs with
    | mnil  => mnil
   (* will not happen *)
    | mtcons _ _ ph ptl => mtcons ph (mSwapEmbed ptl swEmbed)
    | mpcons _ _ ph ptl =>
           mpcons (pSwapEmbed ph  swEmbed) 
                  (mSwapEmbed ptl swEmbed)
  end.


(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)
