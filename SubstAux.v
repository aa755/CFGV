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
Require Export AssociationList.
Set Implicit Arguments.
(* moving the following definition inside the section
    causes issues while transporting a sub.
    Inside a section, SSubstitution is a constant *)
(** CatchFileBetweenTagsSSubstAuxStart *)

Definition SSubstitution {G} (vc : VarSym G):=
  list (vType vc * Term (gsymTN (vSubstType G vc))).

(** CatchFileBetweenTagsSSubstAuxEnd *)

Definition SubFilter {G} {vc : VarSym G} 
  (sub: SSubstitution vc) (lv : list (vType vc))
    : SSubstitution vc
  := (ALFilter (DeqVtype vc) sub lv).

Definition SubKeepFirst {G} {vc : VarSym G} 
  (sub: SSubstitution vc) (lv : list (vType vc))
    : SSubstitution vc
  := (ALKeepFirst (DeqVtype vc) sub lv).

Ltac dalfind :=
  match goal with
    | [ |- context[ALFind (DeqVtype ?vc) ?sub ?v] ] =>
      let o := fresh "o" in
      remember (ALFind (DeqVtype vc) sub v) as o;
        let h := fresh "h" in
        rename_last h;
          destruct o; symmetry in h;
          [ applydup ALFindSome in h
          | applydup ALFindNone in h
          ]
  end.

Fixpoint tSSubstAux {G : CFGV} {vc : VarSym G}
  (gs : (GSym G)) (pt : Term gs)
  (sub : SSubstitution vc) {struct pt} :  Term gs :=
match pt in Term gs return Term gs with
| tleaf a b => tleaf a b 
| vleaf vcc var =>   match DeqVarSym vc vcc with
                     | left eqq => 
                          ALFindDef 
                            (DeqVtype vcc)
                            (transport eqq sub) 
                            var 
                            (vleaf vcc var) (* default value*)
                     | right _ => (vleaf vcc var)
                     end
| tnode p mix => tnode p (mSSubstAux  
                          mix
                          (lBoundVars vc (bndngPatIndices p ) mix) 
                          sub) 
end
with pSSubstAux {G : CFGV} {vc : VarSym G}
  {gs : (GSym G)} (pt : Pattern gs)
  (sub : SSubstitution vc) {struct pt} : Pattern gs  :=
match pt with
| ptleaf a v => ptleaf a v
| pvleaf vcc var => pvleaf vcc var
(** patterns do not have internal bindings 
    (members of [PatProd] do not specify binding info).
   Hence the [nil] *)
| pnode p lpt => pnode p (mSSubstAux lpt [] sub)
| embed p nt => embed p (tSSubstAux nt sub)
end
with mSSubstAux {G : CFGV} {vc : VarSym G}
  (lgs : list (bool * GSym G)) (pts : Mixture lgs)
  (lbvars : list (list (vType vc)))
  (sub : SSubstitution vc)
 {struct pts}
      : Mixture lgs  := 
match pts in Mixture lgs return Mixture lgs with
| mnil  => mnil
| mtcons _ _ ph ptl => 
    match lbvars with
    | [] => mtcons 
              (tSSubstAux ph sub) 
              (mSSubstAux ptl [] sub)
    | lh ::ltl => mtcons
                    (tSSubstAux ph (SubFilter sub lh))
                    (mSSubstAux ptl ltl sub)
    end
| mpcons _ _ ph ptl =>
    match lbvars with
    | [] => mpcons 
              (pSSubstAux ph sub) 
              (mSSubstAux ptl [] sub)
    | lh ::ltl => mpcons
                    (pSSubstAux ph (SubFilter sub lh))
                    (mSSubstAux ptl ltl sub)
    end
end.


Ltac DALFindC sn :=
  unfold ALFindDef;
  match goal with
    | [  |- context[ALFind ?d ?s ?v] ] =>
      let sns := fresh sn "s" in
      remember (ALFind d s v) as sn;
        let h := fresh "Heq" in
        rename_last h;
        destruct sn as [sns |];
          symmetry in h;
          [ applydup ALFindSome in h
          | applydup ALFindNone in h
          ]

  end.

Section GramVC.
Variable G : CFGV.
Variable vc  : VarSym G.



Definition rangeFreeVars (sub : SSubstitution vc) :=
  flat_map (fun t => tfreevars vc t) (ALRange sub).

Lemma rangeFreeVars_cons :
  forall v t s, rangeFreeVars ((v,t)::s) = tfreevars vc t ++ rangeFreeVars s.
Proof.
  unfold rangeFreeVars; simpl; sp.
Qed.

Lemma rangeFreeVarsApp :
  forall sa sb, 
    rangeFreeVars (sa++sb) 
    = rangeFreeVars sa ++ rangeFreeVars sb.
Proof.
  intros.
  unfold rangeFreeVars.
  rewrite <- flat_map_app.
  unfold ALRange.
  rewrite <- map_app.
  refl.
Qed.

Lemma subtractv_subset :
  forall sub l,
    subset (subtractv (rangeFreeVars sub) l) (rangeFreeVars sub).
Proof.
  unfold subtractv; introv.
  apply subset_diff.
  apply subset_app_r; auto.
Qed.
Hint Immediate subtractv_subset.


Lemma SSubstAuxTrivial :
     (  (forall (s : GSym G) (t : Term s) (sub : SSubstitution vc),
            disjoint (tfreevars vc t) (ALDom sub) 
            -> tSSubstAux t sub = t)
         *
        (forall (s : GSym G) (pt : Pattern s) (sub : SSubstitution vc),
            disjoint (pfreevars vc pt) (ALDom sub) 
            -> pSSubstAux pt sub = pt)
         *
        (forall (l : list (bool # GSym G)) (m : Mixture l) 
            (sub : SSubstitution vc)
            (llva : list (list (vType vc))),
            disjoint (mfreevars vc m llva) (ALDom sub) 
            -> mSSubstAux m llva sub = m)).
Proof.
  intros.
  apply GInduction; auto;[| | | | |];
  try (intros; simpl; f_equal; f_equal; auto; fail);
  [| |];
  try( (Case "mtcons" || Case "mpcons");
    introv Hp Hm Hdis;
    allsimpl; destruct llva; allsimpl;
    disjoint_reasoning; f_equal; auto;[];
    f_equal; auto; apply Hp;
    unfold SubFilter; rewrite <- ALDomFilterCommute;
    unfold subtractv in Hdis0;
    apply disjoint_diff_l;
    auto; fail);[].

    introv Hdis. simpl. rename vc0 into vcc.
    destruct_head_match; auto;[].
    subst vcc.
    simpl. rw ALFindDef2Same.
    unfold ALFindDef2. destruct_head_match; auto;[].
    provefalse. destruct s; auto.
    allsimpl. rewrite DeqTrue in Hdis.
    allsimpl. disjoint_reasoning.
    apply Hdis.
    apply ALInEta in l.
    repnd; auto.
Qed.

Corollary SSubstAuxNilNoChange :
     (  (forall (s : GSym G) (t : Term s),
            @tSSubstAux _ vc _ t [] = t)
         *
        (forall (s : GSym G) (pt : Pattern s),
             @pSSubstAux _ vc _ pt [] = pt)
         *
        (forall (l : list (bool # GSym G)) (m : Mixture l) 
            (llva : list (list (vType vc))),
            mSSubstAux m llva [] = m)).
Proof.
  pose proof SSubstAuxTrivial. repnd.
  dands; intros; auto;
  apply_hyp; allsimpl; disjoint_reasoning.
Qed.

Lemma SSubstAuxSubFilter: 
(  (forall (s : GSym G) (t : Term s) (sub : SSubstitution vc) lf,
      disjoint (tfreevars vc t) lf 
      -> tSSubstAux t sub 
          = tSSubstAux t (SubFilter sub lf))
   *
  (forall (s : GSym G) (pt : Pattern s) lf (sub : SSubstitution vc),
      disjoint (pfreevars vc pt) lf 
      -> pSSubstAux pt sub 
          = pSSubstAux pt (SubFilter sub lf))
   *
  (forall (l : list (bool # GSym G)) (m : Mixture l) 
      (llva : list (list (vType vc))) lf (sub : SSubstitution vc),
      disjoint (mfreevars vc m llva) lf 
      -> mSSubstAux m llva sub 
          = mSSubstAux m llva (SubFilter sub lf))).
Proof.
  intros.
  apply GInduction; auto;[| | | | |];
  try(intros; allsimpl;  f_equal; apply H; auto);[ | | ];
  try(introv Hp Hm Hdis;
    allsimpl; destruct llva; allsimpl;
    disjoint_reasoning;f_equal; auto;[];
    unfold SubFilter;
    rw ALFilterSwap;
    rw <- ALFilterAppR;
    rw ALFilterAppAsDiff;
    rw ALFilterAppR; unfold subtractv in Hdis0;
    apply Hp; rw disjoint_diff_l in Hdis0; auto;fail);[].
  - introv Hdis. simpl. rename vc0 into vcc.
    destruct_head_match; auto;[].
    subst vcc.
    simpl. allunfold ALFindDef.
    remember (ALFind (DeqVtype vc) (SubFilter sub lf) v) as alf.
    destruct alf as [als | aln].
    + applysym AssociationList.ALFindFilterSome in Heqalf.
      repnd. rw Heqalf0; auto.
    + applysym AssociationList.ALFindFilterNone in Heqalf.
      dorn Heqalf.
      * rw Heqalf; auto.
      * simpl in Hdis. rewrite DeqTrue in Hdis.
        simpl in Hdis. disjoint_reasoning.
Qed.

Lemma SSubstAuxBVarsDisjoint: 
(  (forall (s : GSym G) (t : Term s) (sub : SSubstitution vc) lf,
      disjoint (tBndngVarsDeep vc t) lf 
      -> disjoint (flat_map (tBndngVarsDeep vc) (ALRange sub)) lf 
      -> disjoint (tBndngVarsDeep vc (tSSubstAux t sub)) lf)
   *
  (forall (s : GSym G) (pt : Pattern s) lf (sub : SSubstitution vc),
      disjoint (pBndngVarsDeep vc pt) lf 
      -> disjoint (flat_map (tBndngVarsDeep vc) (ALRange sub)) lf 
      -> disjoint (pBndngVarsDeep vc (pSSubstAux pt sub)) lf)
   *
  (forall (l : list (bool # GSym G)) (m : Mixture l) 
      (llva : list (list (vType vc))) lf (sub : SSubstitution vc),
      disjoint (mBndngVarsDeep vc m) lf 
      -> disjoint (flat_map (tBndngVarsDeep vc) (ALRange sub)) lf 
      -> disjoint (mBndngVarsDeep vc (mSSubstAux m llva sub)) lf)
).
Proof.
  intros. GInduction; cpx.
  
- Case "vleaf". introv H1d H2d. allsimpl. ddeq; cpx.
  destruct e.
  simpl. unfold ALFindDef. dalfind; cpx.
  rw disjoint_flat_map_l in H2d.
  apply ALInEta in h0; cpx.

- Case "mtcons".
  introv Hypt Hypm H1d H2d. allsimpl. destruct llva; allsimpl; cpx;
  repeat(disjoint_reasoning).
  apply Hypt; repeat(disjoint_reasoning).
  clear H1d H1d0.
  unfold SubFilter. SetReasoning.

- Case "mpcons".
  introv Hypt Hypm H1d H2d. allsimpl. destruct llva; allsimpl; cpx;
  repeat(disjoint_reasoning).
  apply Hypt; repeat(disjoint_reasoning).
  clear H1d H1d0.
  unfold SubFilter. SetReasoning.
Qed.

Definition VarSubSym := gsymTN (vSubstType _ vc).
Ltac DALFind sn :=
  unfold ALFindDef;
  match goal with
    | [  |- context[ALFind ?d ?s ?v] ] =>
      let sns := fresh sn "s" in
      remember (ALFind d s v) as sn;
        destruct sn as [sns |]
    | [ H: context[ALFind ?d  ?s ?v] |- _ ] =>
      let sns := fresh sn "s" in
      remember (ALFind d s v) as sn;
        destruct sn as [sns |]
  end.

Arguments pBndngVars {G} vc {gs} p :  simpl nomatch.
Arguments mBndngVars {G} vc {lgs} pts :  simpl nomatch.
Transparent pBndngVars.
Theorem bindersSSubstAuxNoCnange:
(   forall (s : GSym G) (nt : Term s), True)
*
(   forall (s : GSym G) (pt : Pattern s) (sub : SSubstitution vc),
pBndngVars vc pt = pBndngVars  vc (pSSubstAux pt sub)
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l) 
    (sub : SSubstitution vc) (lbv : list (list (vType vc)))
    (nn : nat),
    getBVarsNth vc m nn = @getBVarsNth 
                            _ vc _ (mSSubstAux m lbv sub) nn
).
 GInduction; allsimpl; introns Hyp; intros; cpx;[ | | ].
  - Case "pnode". simpl. simpl pBndngVars. 
    rewrite mBndngVarsAsNth.
    rewrite mBndngVarsAsNth.
    autorewrite with fast.
    apply eq_flat_maps.
    intros nn Hin. cpx.
  - simpl. destruct nn.
    + simpl. destruct lbv; cpx; simpl.
    + destruct lbv; simpl; cpx; simpl;
       eapply IHm; eauto.
  - simpl. destruct nn.
    + simpl. destruct lbv; cpx; simpl.
    + destruct lbv; simpl; cpx; simpl;
       eapply IHm; eauto.
Qed.

Lemma  lBoundVarsSameSSubstAux : forall
 (l : MixtureParam) (m : Mixture l)
 (sub: SSubstitution vc)
  (la : list (list nat))
  (lbv : list (list (vType vc))),
lBoundVars vc la m
= 
lBoundVars vc la
 (mSSubstAux m 
    lbv sub).
Proof.
  intros.
  apply lBoundVarsSameifNth.
  pose proof bindersSSubstAuxNoCnange.
  cpx.
Qed.

Lemma rangeFreeVarsKeepFirstAppL: forall sub va vb x,
LIn x (rangeFreeVars
        (ALKeepFirst (DeqVtype vc) sub 
           va))
->
LIn x (rangeFreeVars
        (ALKeepFirst (DeqVtype vc) sub 
           (va ++ vb))).
Proof.
  introv Hin.
  rw lin_flat_map in Hin. exrepnd.
  rw in_map_iff in Hin1. exrepnd.
  apply ALKeepFirstLin in Hin1.
  exrepnd.
  rw lin_flat_map. eexists; dands; eauto.
  rw in_map_iff; eexists; dands; eauto;[].
  allsimpl;
  apply ALKeepFirstLin.
  dands; allrw in_app_iff; cpx.
Qed.
 
Lemma rangeFreeVarsKeepFirstAppR: forall sub va vb x,
LIn x (rangeFreeVars
        (ALKeepFirst (DeqVtype vc) sub 
           vb))
->
LIn x (rangeFreeVars
        (ALKeepFirst (DeqVtype vc) sub 
           (va ++ vb))).
Proof.
  introv Hin.
  rw lin_flat_map in Hin. exrepnd.
  rw in_map_iff in Hin1. exrepnd.
  apply ALKeepFirstLin in Hin1.
  exrepnd.
  rw lin_flat_map. eexists; dands; eauto.
  rw in_map_iff; eexists; dands; eauto;[].
  allsimpl;
  apply ALKeepFirstLin.
  dands; allrw in_app_iff; cpx.
Qed.

Lemma rangeFreeVarsKeepFirstAppImplies: forall sub va vb x,
LIn x (rangeFreeVars
        (ALKeepFirst (DeqVtype vc) sub 
           (va++vb)))
->
(LIn x (rangeFreeVars
        (ALKeepFirst (DeqVtype vc) sub 
           (va )))
[+]
LIn x (rangeFreeVars
        (ALKeepFirst (DeqVtype vc) sub 
           (vb )))).
Proof.
  introv Hin.
  rw lin_flat_map in Hin. exrepnd.
  rw in_map_iff in Hin1. exrepnd.
  apply ALKeepFirstAppLin in Hin1.
  dorn Hin1;[left | right];
  rw lin_flat_map; eexists; dands; eauto;
  rw in_map_iff; eexists; dands; eauto.
Qed.
  


Hint Resolve subset_app_l subset_app_r 
rangeFreeVarsKeepFirstAppL rangeFreeVarsKeepFirstAppR:
 slow.
(* In the mixture case, the [lln] actually is
    a function only on m because of the
    way SSubstAux works. In other words,
    the computation of [lBoundVars] does not
    depend on the substitution being applied.
    So, there is no reason why [lln] should
    be different on each side of the equality *)

Theorem SSubstAuxAppAwap:
(   forall (s : GSym G) (nt : Term s) 
    (suba subb : SSubstitution vc)
    (Hdis : disjoint (ALDom suba)  (ALDom subb)),
      (tSSubstAux nt (suba ++ subb)) 
        = (tSSubstAux nt (subb ++ suba))
)
*
( forall (s : GSym G) (pt : Pattern s) (suba subb : SSubstitution vc)
    (Hdis : disjoint (ALDom suba)  (ALDom subb)),
       (pSSubstAux pt (suba ++ subb)) 
          = (pSSubstAux pt (subb ++ suba))
)
*
( forall (l : list (bool # GSym G)) (m : Mixture l) 
  (lln : list (list (vType vc))) 
  (suba subb : SSubstitution vc)
  (Hdis : disjoint (ALDom suba)  (ALDom subb)),
     (mSSubstAux m lln (suba ++ subb)) 
        = (mSSubstAux m lln (subb ++ suba))
).
Proof.
GInduction; allsimpl; introns Hyp; intros; allsimpl; cpx;
try (f_equal; auto);[| |].

- Case "vleaf".
  simpl. rename vc0 into vcc.
  destruct_head_match; auto;[].
  subst vcc.
  simpl.
  allunfold ALFindDef.
  allrw ALFindApp.
  DALFind a1l; DALFind a2l; cpx;[].
  allapplysym ALFindSome.
  allapply ALInEta; exrepnd.
  disjoint_lin_contra.
- Case "mtcons".
  destruct lln; allsimpl; f_equal; cpx.
  unfold SubFilter. allrw ALFilterAppSub.
  apply Hyp; cpx.
  apply (subset_disjointLR Hyp1);
  SetReasoning.
  (** again, exactly same as the [mtcons] case *)
- Case "mpcons".
  destruct lln; allsimpl; f_equal; cpx.
  unfold SubFilter.
  allrw ALFilterAppSub.
  apply Hyp; cpx.
  apply (subset_disjointLR Hyp1);
  SetReasoning.
Qed.

Hint Resolve lBoundVarsmBndngVars 
  (snd bindersSubsetDeep)
  (snd (fst bindersSubsetDeep))
  (mcase bindersAllvarsSubset)
  (tcase bindersAllvarsSubset)
: SetReasoning.

Hint Unfold  rangeFreeVars
 ALRange : SetReasoning.

(** This operation applies the substitution [subb]
    to each element of the range of the substitution
    [suba]. It is useful in defining the result of
    nested substitutions *)
Definition tSSubstAux_sub (suba subb : SSubstitution vc):=
  ALMapRange (fun t => tSSubstAux t subb) suba.

Lemma tSSubstAuxSubUnfold :
  forall (suba subb : SSubstitution vc),
  tSSubstAux_sub suba subb
  = ALMapRange (fun t => tSSubstAux t subb) suba.
Proof.
  auto.
Qed.


Lemma tSSubstAuxSubFilter:
  forall 
  (suba subb: SSubstitution vc)
  (lv : list (vType vc)),
  disjoint lv (rangeFreeVars suba)
    -> tSSubstAux_sub suba 
          (SubFilter subb lv)
       = tSSubstAux_sub suba subb.
Proof.
  induction suba as [|(v,t) suba Hind];
  introv Hdis ; cpx;[].
  simpl. 
  unfold rangeFreeVars in Hdis.
  simpl in Hdis.
  repeat(disjoint_reasoning).
  f_equal; cpx;[].
  f_equal. symmetry.
  apply SSubstAuxSubFilter. disjoint_reasoning.
Qed.
  

(* in the [Mixture] case, [mSSubstAux] is
  applied to 2 different terms.
  So one might expect the statement to have
  [llm1] and [llm2]. However,
  since [SSubstAux] does not change bound variables,
  the 2 terms will be called with same [llm]
*)

  
Theorem SSubstAuxNestAsApp:
( forall (s : GSym G) (nt : Term s)
  (suba subb : SSubstitution vc)
  (Hdis: disjoint (tBndngVarsDeep vc nt)
                  (rangeFreeVars suba)),
  tSSubstAux (tSSubstAux nt suba) subb
  = tSSubstAux nt 
          (tSSubstAux_sub suba subb ++ subb)
)
*
( forall (s : GSym G) (pt : Pattern s)
  (suba subb : SSubstitution vc)
  (Hdis: disjoint (pBndngVarsDeep vc pt)
                  (rangeFreeVars suba)),
  pSSubstAux (pSSubstAux pt suba) subb
      = pSSubstAux pt 
          (tSSubstAux_sub suba subb ++ subb)
)
*
( forall (l : list (bool # GSym G)) (m : Mixture l) 
  (suba subb : SSubstitution vc)
  (llm : list (list (vType vc)))
  (Hdis: disjoint (mBndngVarsDeep vc m ++ (flatten llm))
                  (rangeFreeVars suba)),
     mSSubstAux (mSSubstAux m llm suba) llm subb
      = mSSubstAux m llm
          ((tSSubstAux_sub suba subb) ++ subb)
).
Proof.
GInduction; allsimpl; introns Hyp; intros; allsimpl; cpx;
  try (f_equal;cpx;fail); allsimpl; repeat (disjoint_reasoning);
 [| | | |].
- Case "vleaf".
  simpl. rename vc0 into vcc; allsimpl;
  destruct_head_match; auto;simpl;
    [|destruct_head_match;cpx; fail].
  rename e into Heq.
  revert v. rw <- Heq.
  intros. simpl.
  DALFind a1l;[|];symmetry in Heqa1l.
  + apply ALFindRangeMapSome with
      (f:=(fun t => tSSubstAux t subb))  in Heqa1l.
    rw ALFindApp.
    unfold tSSubstAux_sub.
    rw Heqa1l; cpx.
  + apply ALFindRangeMapNone with
      (f:=(fun t => tSSubstAux t subb))  in Heqa1l.
    rw ALFindApp.
    unfold tSSubstAux_sub.
    rw Heqa1l; simpl; cpx.
    rewrite DeqTrue.
    cpx.

- Case "tnode".
  f_equal. rw <- lBoundVarsSameSSubstAux.
  apply Hyp.
  repeat(disjoint_reasoning);[].
  SetReasoning.

- Case "pnode".
  f_equal.
  apply Hyp.
  repeat(disjoint_reasoning);[].
  SetReasoning.

- Case "mtcons".
  destruct llm as [| lh llm];allsimpl;f_equal;
  try apply Hyp;
  try apply Hyp0;
  repeat(disjoint_reasoning);
  SetReasoning;[].
  unfold SubFilter.
  rw ALFilterAppSub.
  unfold tSSubstAux_sub.
  rw ALMapRangeFilterCommute.
  rw <- tSSubstAuxSubUnfold.
  rewrite <- tSSubstAuxSubFilter with (lv:=lh);
  repeat(disjoint_reasoning);
  SetReasoning.
  apply Hyp.
  repeat(disjoint_reasoning);
  SetReasoning.

- Case "mpcons".
  destruct llm as [| lh llm];allsimpl;f_equal;
  try apply Hyp;
  try apply Hyp0;
  repeat(disjoint_reasoning);
  SetReasoning;[].
  unfold SubFilter.
  rw ALFilterAppSub.
  unfold tSSubstAux_sub.
  rw ALMapRangeFilterCommute.
  rw <- tSSubstAuxSubUnfold.
  rewrite <- tSSubstAuxSubFilter with (lv:=lh);
  repeat(disjoint_reasoning);
  SetReasoning.
  apply Hyp.
  repeat(disjoint_reasoning);
  SetReasoning.

Qed.


Lemma tSSubstAux_sub_trivial:
forall (suba subb : SSubstitution vc)
(Hdis: disjoint (rangeFreeVars suba) (ALDom subb)),
tSSubstAux_sub suba subb = suba.
Proof.
  induction suba; intros; cpx;[].
  unfold rangeFreeVars in Hdis.
  simpl in Hdis. disjoint_reasoning.
  allsimpl.
  simpl. f_equal; auto;[].
  f_equal.
  apply SSubstAuxTrivial.
  trivial.
Qed.

(* upto alpha equality,
    this is equivalent to [SSubstAux_nest_swap2] 
    for [NTerm]. However contrary, it has fewer
    hypotheses, i.e. the hypotheses about
    freshness of bvars of [suba] and [subb]
    are not required here*)
Theorem SSubstAuxNestSwap:
( forall (s : GSym G) (nt : Term s) 
  (suba subb : SSubstitution vc)
  (H1dis: disjoint (tBndngVarsDeep vc nt)
                  (rangeFreeVars suba 
                    ++ rangeFreeVars subb))
  (H2dis: disjoint (rangeFreeVars suba) 
                   (ALDom subb))
  (H3dis: disjoint (rangeFreeVars subb) 
                   (ALDom suba))
  (H4dis: disjoint (ALDom suba) 
                   (ALDom subb)),
  tSSubstAux (tSSubstAux nt suba) subb
  = tSSubstAux (tSSubstAux nt subb) suba
)
*
( forall (s : GSym G) (nt : Pattern s) 
  (suba subb : SSubstitution vc)
  (H1dis: disjoint (pBndngVarsDeep vc nt)
                  (rangeFreeVars suba 
                    ++ rangeFreeVars subb))
  (H2dis: disjoint (rangeFreeVars suba) 
                   (ALDom subb))
  (H3dis: disjoint (rangeFreeVars subb) 
                   (ALDom suba))
  (H4dis: disjoint (ALDom suba)
                   (ALDom subb)),
  pSSubstAux (pSSubstAux nt suba) subb
  = pSSubstAux (pSSubstAux nt subb) suba
)
*
( forall (mp : MixtureParam) (nt : Mixture mp) 
  (suba subb : SSubstitution vc)
  (llm : list (list (vType vc)))
  (H1dis: disjoint (mBndngVarsDeep  vc nt ++ flatten llm)
                  (rangeFreeVars suba 
                    ++ rangeFreeVars subb))
  (H2dis: disjoint (rangeFreeVars suba) 
                   (ALDom subb))
  (H3dis: disjoint (rangeFreeVars subb) 
                   (ALDom suba))
  (H4dis: disjoint (ALDom suba) 
                   (ALDom subb)),
  mSSubstAux (mSSubstAux nt llm suba) llm subb
  = mSSubstAux (mSSubstAux nt llm subb) llm suba
).
Proof.
  dands; intros;
  try disjoint_reasoning;
  allrw (tcase SSubstAuxNestAsApp);
  allrw (pcase SSubstAuxNestAsApp);
  allrw (mcase SSubstAuxNestAsApp);
  repeat disjoint_reasoning;[| |];

  repeat (rw tSSubstAux_sub_trivial;
              try disjoint_reasoning);
  apply SSubstAuxAppAwap; trivial.
Qed.




Theorem free_vars_SSubstAux:
(   forall (s : GSym G) (nt : Term s) 
    (sub : SSubstitution vc),
    disjoint (tBndngVarsDeep vc nt)
             (rangeFreeVars sub)
    ->  eqset 
          (tfreevars vc (tSSubstAux nt sub))
          (   (diff (DeqVtype vc) (ALDom sub) 
                          (tfreevars vc nt)) 
              ++
              (rangeFreeVars 
                    (SubKeepFirst sub (tfreevars vc nt)))
          )
)
*
( forall (s : GSym G) (pt : Pattern s) (sub : SSubstitution vc),
  disjoint (pBndngVarsDeep vc pt)
           (rangeFreeVars sub)
  ->  eqset 
        (pfreevars vc (pSSubstAux pt sub))
        ( (diff (DeqVtype vc) (ALDom sub) (pfreevars vc pt)) 
          ++
              (rangeFreeVars 
                  (SubKeepFirst sub (pfreevars vc pt)))
         )
)
*
( forall (l : list (bool # GSym G)) (m : Mixture l) 
  (llva : list (list (vType vc))) 
  (sub : SSubstitution vc),
  disjoint (mBndngVarsDeep vc m ++ (flatten llva))
           (rangeFreeVars sub)
  ->  eqset 
        (mfreevars vc (mSSubstAux m llva sub) llva)
        ( (diff (DeqVtype vc) (ALDom sub) (mfreevars vc m llva)) 
           ++
              (rangeFreeVars 
                  (SubKeepFirst sub (mfreevars vc m llva)))
         )
).
Proof.
unfold SubKeepFirst.
  GInduction; allsimpl; introns Hyp; intros; cpx;
  try (simpl; rw diff_nil; rw ALKeepFirstNil; simpl;
      unfold rangeFreeVars, ALRange, ALKeepFirst; simpl;
      split;cpx);[| | | | ].
- Case "vleaf".
    rename vc0 into vcc. rewrite DeqSym.
    destructr (DeqVarSym vc vcc) as [dd|dd]; auto.
    + destruct dd. allsimpl. rewrite DeqTrue.
      allunfold ALFindDef.
    allsimpl. rw diff_cons_r.
    DALFind Hd;symmetry in HeqHd. 
    * applydup ALFindSome in HeqHd.
      apply ALInEta in HeqHd0. repnd.
      apply ALFindSomeKeepFirstSingleton in HeqHd.
      rw HeqHd. unfold rangeFreeVars; auto.
      simpl. rw app_nil_r. rw memberb_din.
      cases_ifd Hd; cpx;[].
      rw diff_nil. simpl.
      unfold eqset. cpx.
    * applydup ALFindNone in HeqHd. simpl. rewrite DeqTrue.
      apply ALFindNoneKeepFirstSingleton in HeqHd.
      rw HeqHd. unfold rangeFreeVars; auto.
      simpl. rw app_nil_r. rw memberb_din.
      cases_ifd Hd; cpx;[].
      rw diff_nil. 
      unfold eqset. cpx.
  + rewrite DeqSym. rw <- HeqHdeq. allsimpl.
    rewrite DeqSym. rw <- HeqHdeq.
    autorewrite with fast. unfold eqset; cpx.
- Case "tnode". 
  unfold allBndngVars.
  rw <- lBoundVarsSameSSubstAux.
  apply Hyp. disjoint_reasoning; cpx;[].
  SetReasoning.

- Case "pnode".
  apply Hyp.
  simpl. autorewrite with fast.
  cpx.
- Case "mtcons". destruct llva as [| llh llva];
   simpl; cpx; unfold subtractv;
   allrw diff_app_r; allsimpl.
  + split.
    * introv Hin; allrw in_app_iff;
      dorn Hin; try (apply Hyp0 in Hin);
      try (apply Hyp in Hin);
      try(rw in_app_iff in Hin); try(dorn Hin);cpx;
      try (apply in_diff in Hin); exrepnd; cpx;
      allsimpl; autorewrite with fast;
      repeat(disjoint_reasoning);[|];
      right; eauto with slow.
    * introv Hin; allrw in_app_iff.
      dorn Hin;[dorn Hin;[left|right]|];
      try apply Hyp0;
      try apply Hyp;
      allrw in_app_iff; 
      allsimpl; autorewrite with fast;
      repeat(disjoint_reasoning);
      cpx;[].
      apply rangeFreeVarsKeepFirstAppImplies
      in Hin.
      dorn Hin;[left|right];
      try apply Hyp0;
      try apply Hyp;
      allrw in_app_iff;allsimpl; autorewrite with fast;
      repeat(disjoint_reasoning);
      cpx; right; cpx.

  + split. 
    * introv Hin. allrw in_app_iff.

      dorn Hin;[ |  apply Hyp0 in Hin;[|];
                    repeat (disjoint_reasoning);[];
                    rw in_app_iff in Hin;
                    dorn Hin; cpx;[];  
                    right; apply rangeFreeVarsKeepFirstAppR; cpx].
      rw in_diff in Hin; exrepnd.
      apply Hyp in Hin0;
      allrw in_app_iff; exrepnd;
      allrw in_app_iff;allsimpl; autorewrite with fast;
      repeat (disjoint_reasoning); 
      unfold SubFilter; try SetReasoning;[| ].



      rename l into Hin0.
      left. left. allrw in_diff; exrepnd; dands; cpx.
      introv Hc. unfold SubFilter in Hin0.
      rw <- ALDomFilterCommute in Hin0.
      allrw in_diff.  apply Hin0.
      dands; cpx.

      rename l into Hin0.
      right. apply rangeFreeVarsKeepFirstAppL.
      SetReasoning.
      rw ALKeepFirstFilterDiff;
      auto.
    
    * introv Hin. allrw in_app_iff.
      dorn Hin;[dorn Hin|];[ | | ].

      left. allrw in_diff. exrepnd.
      dands; cpx;[]. unfold SubFilter.
      apply Hyp. 


      repeat(disjoint_reasoning); SetReasoning.

      allrw in_app_iff.
      left. allrw in_diff. exrepnd.
      dands; cpx;[].
      rw <- ALDomFilterCommute.
      rw in_diff. introv Hc.
      apply Hin. exrepnd. cpx; fail.

      allrw in_diff. right.
      exrepnd; cpx.
      apply Hyp0;repeat(disjoint_reasoning).
      allrw in_diff. allrw in_app_iff.
      allrw in_diff.
      left; cpx; fail.

      apply rangeFreeVarsKeepFirstAppImplies in Hin.
      dorn Hin;[left|right].

      allrw in_diff.
      dands; cpx.
      apply Hyp;[repeat(disjoint_reasoning);
      unfold SubFilter; SetReasoning; fail|].

      allrw in_app_iff.
      allrw in_diff.
      right. SetReasoning.
      rw ALKeepFirstFilterDiff.
      eauto.

      repeat(disjoint_reasoning).
      apply Hyp3 in X.
      apply X. SetReasoning; fail.


      apply Hyp0;repeat(disjoint_reasoning);[].
      allrw in_app_iff.
      allrw in_diff.
      right.
      auto.
(** exactly same as the mtcons case *)
- Case "mpcons". destruct llva as [| llh llva];
   simpl; cpx; unfold subtractv;
   allrw diff_app_r; allsimpl.
  + split.
    * introv Hin; allrw in_app_iff;
      dorn Hin; try (apply Hyp0 in Hin);
      try (apply Hyp in Hin);
      try(rw in_app_iff in Hin); try(dorn Hin);cpx;
      try (apply in_diff in Hin); exrepnd; cpx;
      allsimpl; autorewrite with fast;
      repeat(disjoint_reasoning);[|];
      right; eauto with slow.
    * introv Hin; allrw in_app_iff.
      dorn Hin;[dorn Hin;[left|right]|];
      try apply Hyp0;
      try apply Hyp;
      allrw in_app_iff; 
      allsimpl; autorewrite with fast;
      repeat(disjoint_reasoning);
      cpx;[].
      apply rangeFreeVarsKeepFirstAppImplies
      in Hin.
      dorn Hin;[left|right];
      try apply Hyp0;
      try apply Hyp;
      allrw in_app_iff;allsimpl; autorewrite with fast;
      repeat(disjoint_reasoning);
      cpx; right; cpx.

  + split. 
    * introv Hin. allrw in_app_iff.

      dorn Hin;[ |  apply Hyp0 in Hin;[|];
                    repeat (disjoint_reasoning);[];
                    rw in_app_iff in Hin;
                    dorn Hin; cpx;[];  
                    right; apply rangeFreeVarsKeepFirstAppR; cpx].
      rw in_diff in Hin; exrepnd.
      apply Hyp in Hin0;
      allrw in_app_iff; exrepnd;
      allrw in_app_iff;allsimpl; autorewrite with fast;
      repeat (disjoint_reasoning); 
      unfold SubFilter;try SetReasoning;[|].



      rename l into Hin0.
      left. left. allrw in_diff; exrepnd; dands; cpx.
      introv Hc. unfold SubFilter in Hin0.
      rw <- ALDomFilterCommute in Hin0.
      allrw in_diff.  apply Hin0.
      dands; cpx.

      rename l into Hin0.
      right. apply rangeFreeVarsKeepFirstAppL.
      SetReasoning.
      rw ALKeepFirstFilterDiff;
      auto.
    
    * introv Hin. allrw in_app_iff.
      dorn Hin;[dorn Hin|];[ | | ].

      left. allrw in_diff. exrepnd.
      dands; cpx;[].
      apply Hyp. 


      repeat(disjoint_reasoning);
      unfold SubFilter; SetReasoning.

      allrw in_app_iff.
      left. allrw in_diff. exrepnd.
      dands; cpx;[]. unfold SubFilter.
      rw <- ALDomFilterCommute.
      rw in_diff. introv Hc.
      apply Hin. exrepnd. cpx; fail.

      allrw in_diff. right.
      exrepnd; cpx.
      apply Hyp0;repeat(disjoint_reasoning).
      allrw in_diff. allrw in_app_iff.
      allrw in_diff.
      left; cpx; fail.

      apply rangeFreeVarsKeepFirstAppImplies in Hin.
      dorn Hin;[left|right].

      allrw in_diff.
      dands; cpx.
      apply Hyp;[repeat(disjoint_reasoning);
      unfold SubFilter;SetReasoning; fail|].

      allrw in_app_iff.
      allrw in_diff.
      right. SetReasoning.
      rw ALKeepFirstFilterDiff.
      eauto.

      repeat(disjoint_reasoning).
      apply Hyp3 in X.
      apply X. SetReasoning; fail.


      apply Hyp0;repeat(disjoint_reasoning);[].
      allrw in_app_iff.
      allrw in_diff.
      right.
      auto.
Qed.


Lemma in_ALRange_ALFilter_implies :
  forall (sub : SSubstitution vc) l,
    subset
      (ALRange (SubFilter sub l))
      (ALRange sub).
Proof.
  unfold SubFilter.
  unfold subset, ALRange; introv i.
  allrw in_map_iff; exrepnd; allsimpl; subst.
  exists (a0,a); simpl; sp.
  allapply ALFilterLIn; sp.
Qed.

Lemma rangeFreeVars_ALFilter_subset :
  forall (sub : SSubstitution vc) l,
    subset (rangeFreeVars (SubFilter sub l))
           (rangeFreeVars sub).
Proof.
  introv i.
  allunfold rangeFreeVars.
  allrw lin_flat_map; exrepnd.
  exists x0; sp.
  allapply in_ALRange_ALFilter_implies; sp.
Qed.


End GramVC.



(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)

(*
Lemma SSubstAuxFVarsDisjoint: (
(forall (s : GSym G) (t : Term s) (sub : SSubstitution vc) lf,
    disjoint (tfreevars vc t) lf 
    -> disjoint (rangeFreeVars sub) lf 
    -> disjoint (tfreevars vc (tSSubstAux t sub)) lf)
 *
(forall (s : GSym G) (pt : Pattern s) lf (sub : SSubstitution vc),
    disjoint (pfreevars vc pt) lf 
    -> disjoint (rangeFreeVars sub) lf 
    -> disjoint (pfreevars vc (pSSubstAux pt sub)) lf)
 *
(forall (l : list (bool # GSym G)) (m : Mixture l) 
    (llva : list (list (vType vc))) lf (sub : SSubstitution vc),
    disjoint (mfreevars vc m llva) lf 
    -> disjoint (rangeFreeVars sub) lf 
    -> disjoint (mfreevars vc (mSSubstAux m llva sub) llva) lf)
).
Proof.
  intros. GInduction; cpx.
  
- Case "vleaf". introv H1d H2d. allsimpl.
  rewrite DeqSym in H1d.
  ddeq; allsimpl;[| ddeq]; cpx;[].
  destruct e;  allsimpl; cpx.
  simpl. unfold ALFindDef. dalfind; allsimpl;
    [| rewrite DeqTrue]; cpx.
  rw disjoint_flat_map_l in H2d.
  apply ALInEta in h0; cpx.

*)
