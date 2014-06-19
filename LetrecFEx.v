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
Set Implicit Arguments.

Inductive VarSym : Set :=  tmVSym | tyVSym.
Inductive TNonTerminal : Set := term | type .
Definition vSubstType (vc : VarSym) : TNonTerminal :=
match vc with  
  tmVSym => term  | tyVSym => type 
end.

Inductive Terminal :Set := .
Inductive PNonTerminal : Set := | lasgn | asgn | asgnRhs.


Inductive PatProd : Set :=  | aNil | aCons | asgnP.

Inductive EmbedProd : Set := | asgnRhsE.

Definition EmbedLhsRhs  (_: EmbedProd)
: (PNonTerminal * TNonTerminal) := (asgnRhs, term).

Notation inrr := (fun x => inr (inr x)).
Notation inlr := (fun x => inl (inr x)).
Notation inll := (fun x => inl (inl x)).

(**
Definition ppLhsRhs (p:PatProd) :
 (PNonTerminal * list (PNonTerminal+ (Terminal + VarSym))):= 
match p with
|aNil => (lasgn,[])
|aCons => (lasgn, [inl lasgn, inl asgn])
|asgnP  => (asgn, [inrr vsym, inl asgnRhs])
end.

Inductive TermProd : Set := | app | lam | letr.

Definition tpLhsRhs (p:TermProd) :
 (TNonTerminal * 
    list ((PNonTerminal + VarSym) + (Terminal + TNonTerminal))):= 
match p with
|app => (term,[inrr term, inrr term])
|lam => (term, [inlr vsym, inrr term])
|letr  => (term, [inll lasgn, inrr term])
end.

Definition bindingInfo (p:TermProd) : list (nat * nat) :=
match p with
|app => []
|lam => [(0,1)]
|letr  => [(0,0),(0,1)]
end.

Definition letrecCFGV : CFGV.
eapply Build_CFGV
      with   (VarSym := VarSym)
             (Terminal := Terminal)
             (PNonTerminal := PNonTerminal)
             (TNonTerminal := TNonTerminal)
             (PatProd := PatProd)
             (TermProd := TermProd)
             (tpLhsRhs := tpLhsRhs)
             (bindingInfo := bindingInfo)
             (EmbedProd := EmbedProd).
  - intro. exact NVarSpec.
  - intro. intro. destruct x. destruct y. auto.
  - exact vSubstType.
  - intro H. contradiction.
  - exact ppLhsRhs.
  - exact EmbedLhsRhs.
  - admit.
  - intro. intro. destruct x. destruct y. auto.
  - intro H. contradiction.
  - intro. intro. destruct x. destruct y. auto.
  - intro. intro. destruct x; destruct y; 
    try (left; cpx; fail); (try right; introv Hc; inverts Hc ; cpx).
  - intro. intro. destruct x; destruct y; 
    try (left; cpx; fail); (try right; introv Hc; inverts Hc ; cpx).
  - intro. intro. destruct x; destruct y; 
    try (left; cpx; fail); (try right; introv Hc; inverts Hc ; cpx).
  - intro. intro. destruct x; destruct y; 
    try (left; cpx; fail); (try right; introv Hc; inverts Hc ; cpx).
Defined.

Definition letrxxx : @Term letrecCFGV (@gsymTN letrecCFGV term).
Proof.
  apply (@tnode letrecCFGV letr). apply (mpcons).
  - simpl. apply (@pnode letrecCFGV aCons); simpl.
    apply (mpcons); simpl.
    + apply (@pnode letrecCFGV aNil). simpl. apply mnil.
    + apply (mpcons); [| apply mnil].
      apply (@pnode letrecCFGV asgnP). simpl.
      apply (mpcons).
      * apply pvleaf. simpl. exact nvarx.
      * apply (mpcons);[| apply mnil].
        apply (@embed letrecCFGV asgnRhsE). simpl.
        apply (@vleaf letrecCFGV vsym).
        exact nvarx.
  - simpl. apply (mtcons);[| apply mnil].
    apply (@vleaf letrecCFGV vsym).
    exact nvarx.
Defined.
*)
