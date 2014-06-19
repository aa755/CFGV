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
Require Export CFGV.
Set Implicit Arguments.

(** printing #  $\times$ #×# *)
(** printing &  $\times$ #×# *)

Notation inrr := (fun x => inr (inr x)).
Notation inlr := (fun x => inl (inr x)).
Notation inll := (fun x => inl (inl x)).

(** CatchFileBetweenTagsLetRecStart *)

Inductive PNonTerminal : Set :=  lasgn | asgn | asgnRhs.
Inductive VarSym : Set := vsym.
Inductive TNonTerminal : Set := term.
Inductive Terminal :Set := .
Definition vSubstType (_ : VarSym) : TNonTerminal := term.

Inductive PatProd : Set := aNil | aCons | asgnP.
Inductive TermProd : Set := app | lam | letr.
Inductive EmbedProd : Set := asgnRhsE.
Definition epLhsRhs  (_: EmbedProd):
   (PNonTerminal * TNonTerminal) := (asgnRhs, term).

Definition ppLhsRhs (p:PatProd) :
 (PNonTerminal * list (PNonTerminal+ (Terminal + VarSym))):=
match p with
 | aNil => (lasgn,[])
 | aCons => (lasgn, [inl lasgn, inl asgn])
 | asgnP  => (asgn, [inrr vsym, inl asgnRhs])
end.
Definition tpLhsRhs (p:TermProd) :
 (TNonTerminal * list ((PNonTerminal + VarSym)
                         + (Terminal + TNonTerminal))):=
match p with
 | app => (term,[inrr term, inrr term])
 | lam => (term, [inlr vsym, inrr term])
 | letr  => (term, [inll lasgn, inrr term])
end.

Definition bindingInfo (p:TermProd) : list (nat * nat) :=
match p with
 | app => []  | lam => [(0,1)]  | letr  => [(0,0),(0,1)]
end.
(** CatchFileBetweenTagsLetRecEnd *)

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
  - intro. exact nvarVarType.
  - exact vSubstType.
  - exact ppLhsRhs.
  - exact epLhsRhs.
  - proveBindingInfoCorrect.
  - proveDeqInductiveNonrec. 
  - intro H. contradiction.
  - proveDeqInductiveNonrec.
  - proveDeqInductiveNonrec.
  - proveDeqInductiveNonrec.
  - proveDeqInductiveNonrec.
  - proveDeqInductiveNonrec.
  - proveDeqInductiveNonrec.
Grab Existential Variables.
intro t. inverts t.
Defined.

Require Export Term.

(** a representation of the term 
  
  letrec x:=y in z

*)
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
        exact nvary.
  - simpl. apply (mtcons);[| apply mnil].
    apply (@vleaf letrecCFGV vsym).
    exact nvarz.
Defined.



(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)
