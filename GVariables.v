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
Require Export AssociationList.
(** printing #  $\times$ #×# *)
(** printing &  $\times$ #×# *)

(** CatchFileBetweenTagsVarTypeStart *)
Record VarType := {
  typ : Type;  eqdec : Deq typ;
  fresh : forall (avoid : list typ) (sugg : list typ),typ; 
  freshCorrect: forall (avoid : list typ) 
    (sugg : list typ), !(LIn (fresh avoid sugg) avoid)
}.
(** CatchFileBetweenTagsVarTypeEnd *)

(* This predicate denotes that a type
    is suitable to serve
    as a collection of variable names.
    The equality should be decidable
    and it should be always possible
    to pick a fresh name.
    
    The definition of [fresh] should
    not use any opaque definitions/lemmas.

    What about efficiency?
    Can we replace the list with a binary
    (search) tree?
    we will need an ordering then too.
 *)


Fixpoint FreshDistinctRenamings
  (VT : VarType) 
  (lv :list (typ VT ))
  (lvAvoid :list (typ VT ))
  {struct lv}
  : (AssocList (typ VT ) (typ VT )) :=
match  lv with
  | [] => []
  | vh :: vtl =>
    let newvar :=  ((fresh VT) lvAvoid [vh]) in
    (vh,newvar) :: (FreshDistinctRenamings
               VT vtl (newvar :: lvAvoid))
end.

Lemma FreshDistRenSpec: forall
  (VT : VarType) 
  (lv :list (typ VT ))
  (lvAvoid :list (typ VT )),
  let sw := (FreshDistinctRenamings VT lv  lvAvoid) in
  no_repeats (ALRange sw) 
  # disjoint (ALRange sw) lvAvoid 
  # ALDom sw = lv.
Proof.
  induction lv as [| h tl Hind]; intros; 
  [dands; cpx|].
  allsimpl. destruct VT; allsimpl.
  exrepnd.
  allsimpl.
  specialize (Hind ((fresh0 lvAvoid [h]):: lvAvoid)).
  repnd; allsimpl.
  dands; try econstructor; eauto; try congruence.
  - apply disjoint_sym in Hind1.
    apply Hind1; cpx.
  - repeat (disjoint_reasoning).
Defined.
    
(* might not compute.
    saves time in proofs.
    destruction of it gives the properties too *)
Lemma FreshDistRenWSpec: forall
  (VT : VarType) 
  (lv :list (typ VT ))
  (lvAvoid :list (typ VT )),
  {lvn : list (typ VT ) $
  no_repeats lvn # disjoint lvn lvAvoid 
  # length lvn= length lv}.
Proof.
  intros.
  eexists (ALRange (FreshDistinctRenamings VT lv  lvAvoid)).
  pose proof (FreshDistRenSpec VT lv lvAvoid) as XX.
  allsimpl. exrepnd.
  apply (f_equal (@length _ )) in XX.
  allunfold ALDom.
  allunfold ALRange.
  autorewrite with fast.
  autorewrite with fast in XX.
  dands; cpx.
Defined.


Fixpoint FreshDistinctVars
  (T :VarType)
  (lv :list (typ T))
  (lvAvoid :list (typ T))
  {struct lv}
  : (list (typ T)) :=
match  lv with
  | [] => []
  | vh :: vtl =>
    let newvar :=  ((fresh T) lvAvoid [vh]) in
    newvar :: (FreshDistinctVars
               T vtl (newvar :: lvAvoid))
end.

Lemma FreshDistVarsSpec: forall
  {T : VarType}
  (lv :list (typ T))
  (lvAvoid :list (typ T)),
  let lvn := (FreshDistinctVars T lv  lvAvoid) in
  no_repeats lvn # disjoint lvn lvAvoid # length lvn= length lv.
Proof.
  induction lv as [| h tl Hind]; intros; subst lvn; 
  [dands; cpx|].
  allsimpl. destruct T. allsimpl.
  exrepnd.
  allsimpl.
  specialize (Hind ((fresh0 lvAvoid [h]):: lvAvoid)).
  repnd; allsimpl.
  dands; try econstructor; eauto; try congruence.
  - apply disjoint_sym in Hind1.
    apply Hind1; cpx.
  - repeat (disjoint_reasoning).
Defined.


Require Export variables.

Definition nvarVarType: VarType.
Proof.
  eapply Build_VarType with 
    (typ:=NVar)
    (fresh:= (fun (la ls : list NVar) =>  fresh_var la))
                  ; eauto with Deq.
  intros.
  apply fresh_var_not_in.
Defined.

(** Transparent versions of the one in the standard
    library *)
Hint Resolve nvarVarType : VarType.

  Lemma map_length : forall {A B} (f: A->B) (l : list A), 
    length (map f l) = length l.
  Proof.
    induction l; simpl; auto.
  Defined.
  Lemma seq_length : forall len start, length (seq start len) = len.
  Proof.
    induction len; simpl; auto.
  Defined.

Hint Rewrite  seq_length : fast.

Require Import String.
Require Import Ascii.

Lemma nat2string :forall (n: nat) , string.
Proof.
  intros.
  induction n.
  - exact "1".
  - exact (IHn++"1").
Defined.

Definition shead  (ls: list string) : string :=
match ls with
| [] => ""
| h::tl => h
end.

Fixpoint lmax (l : list nat) :=
match l with
| [] => 0
| h::tl => max h (lmax tl)
end .
Lemma lmaxSpec : forall (l : list nat),
  lforall (fun n=> n <= lmax l) l.
Proof.
  intros. apply lForallSame.
  induction l; cpx.
  allsimpl. dands; cpx.
  - apply Max.le_max_l.
  - apply lForallSame.
    apply lForallSame in IHl.
    eapply implies_lforall; eauto.
    introv H Hlt; allsimpl; cpx.
    apply NPeano.Nat.max_le_compat_l with (p:= a) in Hlt.
    pose proof (Max.le_max_r a a0).
    omega.
Qed.

Lemma lmaxSpecLen : forall (l : list string),
  lforall (fun a=> length a <= lmax (map length l)) l.
Proof.
  introv Hin.
  assert (LIn (length a) (map length l)) as Hl by
  (apply in_map_iff; eexists; eauto).
  simpl. apply lmaxSpec.
  trivial.
Qed.

Lemma lengthAppendStr :
  forall (l1 l2 : string) , length (l1++l2) = length l1 + length l2.
Proof.
  induction l1; trivial.
  intros. simpl. auto.
Qed.

Fixpoint freshStringAux (maxLen: nat) 
  (avoid : list string)
  (sugg : list string) :=
match maxLen with
| 0 => shead (sugg)
| S n => let rs := freshStringAux n avoid sugg
         in match (memberb string_dec rs avoid) with
            | true => rs ++ "1"
            | false => rs
            end
end.

Definition freshString
  (avoid : list string)
  (sugg : list string) :=
  freshStringAux (S (lmax (map length avoid) 
          - length (shead sugg))) avoid sugg.


Lemma freshStringAuxSpec:
  forall sugg (avoid : list string) lm,
  !LIn (freshStringAux lm  avoid sugg) avoid
  [+] (length (freshStringAux lm avoid sugg) 
      = (length (shead sugg) + lm)%nat).
Proof.
  unfold freshString.
  induction lm; cpx.
  intros. allsimpl. rewrite memberb_din.
  cases_ifd Hd; cpx.
  dorn IHlm; cpx.
  right.
  rewrite lengthAppendStr.
  simpl. omega.
Qed.

Lemma freshStringSpec:
  forall (avoid : list string) sugg,
  !LIn (freshString  avoid sugg) avoid.
Proof.
  unfold freshString.
  intros.
  pose proof (freshStringAuxSpec sugg avoid
              (S (lmax (map length avoid) - length (shead sugg))))
              as Hfs.
  dorn Hfs; cpx.
  fold (freshString avoid sugg).
  fold (freshString avoid sugg) in Hfs.
  assert (length (shead sugg) + 
      S (lmax (map length avoid) - length (shead sugg))
  > (lmax (map length avoid))) as XX by omega.
  rewrite <- Hfs in XX.
  introv Hc.
  apply lmaxSpecLen in Hc.
  omega.
Qed.
  
Lemma StringVar : VarType.
Proof.
  eapply Build_VarType with 
      (typ:=string)
      (fresh:=freshString).
  - exact string_dec.
  - exact freshStringSpec.
Qed.


(* only commented code below *)
(*
Fixpoint FreshDistinctRenListList
  {T :Type} (ft : FreshType T) 
  (llv : list (list T))
  (lvAvoid :list T)
  {struct llv}
  : list (AssocList T T) :=
match  llv with
  | [] => []
  | lvh :: lvtl =>
    let ren :=  (FreshDistinctRenamings ft lvh lvAvoid) in
    ren :: (FreshDistinctRenListList
               ft lvtl ((ALRange ren) ++ lvAvoid) )
end.

Lemma FreshDistRenLLSpec: forall
  {T :Type} (ft : FreshType T) 
  (llv : list (list T))
  (lvAvoid :list T),
  let llsw := (FreshDistinctRenListList ft llv lvAvoid) in
  let rangeVars := flat_map (@ALRange _ _) llsw in
  no_repeats rangeVars 
  # disjoint rangeVars lvAvoid
  # map (@ALDom _ _) llsw = llv.
Proof.
  induction llv as [|lvh lvtl Hind]; cpx;[].
  intros. subst llsw. subst rangeVars.
  specialize 
    (Hind (ALRange (FreshDistinctRenamings ft  lvh lvAvoid) ++ lvAvoid)).
  pose proof (FreshDistRenSpec ft lvh lvAvoid) as XXh.
  allsimpl. exrepnd.
  repeat(disjoint_reasoning).
  - apply no_repeats_app. dands; cpx.
    repeat(disjoint_reasoning); cpx.
  - f_equal; cpx.
Qed.

Lemma FreshDistRenLLSpec2: forall
  {T :Type} (ft : FreshType T) 
  (llv : list (list T))
  (lvAvoid :list T),
  let llsw := (FreshDistinctRenListList ft llv lvAvoid) in
  let rangeVars := flat_map (@ALRange _ _) llsw in
  no_repeats rangeVars 
  # disjoint rangeVars lvAvoid
  # flat_map (@ALDom _ _) llsw = flatten llv.
Proof.
  induction llv as [|lvh lvtl Hind]; cpx;[].
  intros. subst llsw. subst rangeVars.
  specialize 
    (Hind (ALRange (FreshDistinctRenamings ft  lvh lvAvoid) ++ lvAvoid)).
  pose proof (FreshDistRenSpec ft lvh lvAvoid) as XXh.
  allsimpl. exrepnd.
  repeat(disjoint_reasoning).
  - apply no_repeats_app. dands; cpx.
    repeat(disjoint_reasoning); cpx.
  - f_equal; cpx.
Qed.
Ltac AddFDLLSpec :=
  let FdSpec := fresh "FdSpec" in 
  let FdLL := fresh "FdLL" in 
  match goal with
  [ |- context [FreshDistinctRenListList ?ft ?llv ?lvA] ]
    => pose proof (FreshDistRenLLSpec ft llv lvA) as FdSpec;
        simpl in FdSpec;
     remember (FreshDistinctRenListList ft llv lvA) as FdLL

  end.

*)



(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)
