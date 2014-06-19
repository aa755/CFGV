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
Require Import CFGV.

(** Now, specialize the previous CFGV to
  CFGVs where the symbols are denoted by strings.
  The goal is to make the specification
  of a [StringCFGV] to be as close as that to 
  paper-pen presentations, i.e. the user has to
  specify the minimal amount of information ans
  proofs are filled automatically.
  We have a decision procedure that takes a [StringCFGV]
  and either produces [CFGV] or produces a proof that
  something is wrong with the input*)

Record StringVarSpec := mksvs {
  vname : String.string;
  subTNonTerminal : String.string;
  vSemType :  {T:Type $ VarType T}
}.

Record Terminal := mkst {
  tname : String.string;
  tSemType :  Type
}.

Record TermProd := mkp {
  pname : String.string;
  tpLhs : String.string;
  prhs : list String.string
}.

Record BindingInfo := mkbind {
  binder : nat;
  bindee : nat
}.

Record StringCFGV := mk_ott {
  (** all the lists below should have distinct elements *)
  VarSymes : list StringVarSpec;
  Terminals : list Terminal;
  TNonTerminals : list String.string;
  Patterns : list String.string;
  (** lhs and elements of rhs of the 3 kinds of 
    production rules below must be members
    of one of the lists above, 
    with some restrictions noted below *)
  PatProds : list TermProd; 
  Embeddings : list TermProd;
  GProds : list (TermProd * (list BindingInfo))
}.

Hint Resolve String.string_dec : Deq.
Definition stSubset (l r : list String.string) : [univ] 
  := (diff  String.string_dec r l = []).

Definition stMinus (l r : list String.string) 
    : list String.string
  := (diff  String.string_dec r l).

Example exxxxxxx: stSubset ["hello"] ["hello", "how"].
Proof.  refl.
Qed.

Definition ProdRhs (sg :StringCFGV) :=
  (TNonTerminals sg) ++ (Patterns sg) ++
  (map vname (VarSymes sg)) 
  ++ (map tname (Terminals sg)).
  
Definition PatProdRhs (sg :StringCFGV) :=
  (Patterns sg) ++
  (map vname (VarSymes sg)) 
  ++ (map tname (Terminals sg)).

 
(*  no_repeats (VarSymes sg)
  # no_repeats (Terminals sg)
  # no_repeats (TNonTerminals sg)
  # no_repeats (Patterns sg) *)

(** We can now use coq's definitional equality to 
    check the properties required to get a [CFGV]
    from [StringCFGV]. The idea is that
    for concrete [StringCFGV]s 
    the proof of the predicate below should
    just be a tuple of [eq_refl].*)
Definition GoodStringCFGV (sg :StringCFGV) :=
  []= (stMinus (map tpLhs (PatProds sg)) (Patterns sg))
      ++ (stMinus (flat_map prhs (PatProds sg)) (PatProdRhs sg))
      ++ (stMinus (map tpLhs (Embeddings sg)) (Patterns sg))
      ++ (stMinus (flat_map prhs (Embeddings sg)) (TNonTerminals sg)).
