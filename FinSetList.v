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
(** Given a list with no repeated elements 
    (upto propositional equality), how do we
    construct type (set) containing  exactly 
    those elements?
    Here is one attempt, that seems to work atleast
    when the underlying type has decidable equality *)

Require Import list.


Definition FinSetList {A : Type} (l: list A):=
 {a : A $ LIn a l}.

(** Here is what we wish to prove *)
Lemma FinSetListCardinality :
  forall {A : Type} (deqa: Deq A) (l: list A),
    no_repeats l
    -> equipollent (FinSetList l) (Fin (length l)).
Abort.

(** Here is a small example that make it seem that it is
    true atleast for particular lists *)

Fixpoint natPrefix (n:nat) :=
match n with
|0 => []
| S m => (natPrefix m) ++ [m]
end.

(** reproving it to avoid opaqe lemmas *)
Lemma in_app_iff :
  forall A l l' (a:A),
    LIn a (l++l') <=> (LIn a l) [+] (LIn a l').
Proof.
  induction l as [| a l]; introv; simpl; split; introv Hyp;
  repeat(in_reasoning); try (contradiction); auto.
  - apply IHl in Hyp. dorn Hyp; auto.
  - right. apply IHl. auto.
  - right. apply IHl. auto.
Defined.


Lemma fin_Set_bijf : forall m, FinSetList (natPrefix m)  -> (Fin m).
Proof.
  unfold FinSetList. induction m as [| m Hind]; introv Hl; exrepnd;[allsimpl;contradiction |].
  allsimpl. exrepnd. apply in_app_iff in Hl0. allsimpl. 
  dorn Hl0;[|dorn Hl0];try(contradiction).
  - exrepnd. assert ({n : nat $ LIn n (natPrefix m)}) as Harg by eauto.
    apply Hind in Harg. exrepnd. allunfold Fin. destruct Harg as [marg MP].
    exists marg. destruct (lt_dec marg m);[| contradiction].
    cases_ifd Hd;[trivial|]. destruct Hdf. apply lt_S; trivial.
  - subst. exists a. cases_ifd Hd;[constructor|]. destruct Hdf.
    auto.
Defined.

Lemma fin_Set_bijg : forall m,  (Fin m) -> FinSetList (natPrefix m).
Proof.
  unfold FinSetList. induction m as [| m Hind]; unfold Fin; introv Hl; exrepnd;
  [destruct m; allsimpl; try contradiction |].
  allsimpl. revert Hl0; cases_ifd Hd; introv Hxx; try contradiction.
  unfold lt in Hdt. apply le_lt_eq_dec in Hdt.
  dorn Hdt.
  - apply lt_S_n in Hdt. assert (Fin m )  as Hf by
    (exists m0; cases_if; auto; try contradiction).
    apply Hind in Hf. exrepnd. exists a.
    apply in_app_iff. left; auto.
  - exists m. apply in_app_iff. right; auto. simpl. auto.
Defined.


Lemma fin_Set : bijection (fin_Set_bijf 3) (fin_Set_bijg 3).
Proof.
  unfolds_base. unfold Fin; dands; unfolds_base; intro s.
  - unfold FinSetList in s.
    simpl in s. exrepnd. repeat(in_reasoning); try contradiction;
    subst; simpl; refl.
  - simpl in s. exrepnd. revert s0.
    destruct m;[|destruct m].
    + simpl. intro; destruct s0; auto.
    + simpl. intro; destruct s0; auto.
    + simpl. destruct m.
      * intro; destruct s0; auto.
      * intro. simpl in s0. inverts s0.
Qed.

Lemma exampleFinListEqui :
  equipollent  (FinSetList (natPrefix 3)) (Fin 3).
Proof.
  unfolds_base.
  eexists. eexists. eapply fin_Set.
Qed.

(** The general lemma [FinSetListCardinality] above,
    or even replacing 3 by a qualtified number in 
    [exampleFinListEqui]
    makes the proof messy because we cannot
    prove it merely by computation anymore. *)
