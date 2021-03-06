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

