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
(*
Corollary free_vars_SSubstAux2:
(   forall (s : GSym G) (nt : Term s) (sub : SSubstitution vc) v,
      LIn v (tfreevars (tSSubstAux nt sub) vc)
      -> (LIn v (tfreevars nt vc) # ! LIn v (ALDom sub))
              [+] {v' : (vType vc)
                   $ {t : Term VarSubSym
                   $ LIn (v',t) sub 
                        # LIn v' (tfreevars nt vc) 
                        # LIn v (tfreevars t vc)}}
)
*
(   forall (s : GSym G) (pt : Pattern s) (sub : SSubstitution vc) v,
      LIn v (pfreevars (pSSubstAux pt sub) vc)
      -> (LIn v (pfreevars pt vc) # ! LIn v (ALDom sub))
              [+] {v' : (vType vc)
                   $ {t : Term VarSubSym
                   $ LIn (v',t) sub 
                        # LIn v' (pfreevars pt vc) 
                        # LIn v (tfreevars t vc)}}
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l) 
      (llva : list (list (vType vc))) (sub : SSubstitution vc) v,
      LIn v (mfreevars (mSSubstAux m llva sub)  vc llva)
      -> (LIn v (mfreevars m vc llva) # ! LIn v (ALDom sub))
              [+] {v' : (vType vc)
                   $ {t : Term VarSubSym
                   $ LIn (v',t) sub 
                        # LIn v' (mfreevars m vc llva) 
                        # LIn v (tfreevars t vc)}}
).
Proof.
  intros.
  apply GInduction; introv Hin; allsimpl; cpx;[| | |].
  - rename vc0 into vcc. rewrite DeqSym.
    destruct (DeqVarSym vc vcc); auto.
    + destruct e. allsimpl.
Abort.
(** The proof below shows variable capture happening
    live at the Abort.
    The lhs of eqset is missing a variable
    because it got captured.

    To actually prove this lemma, we need 
    an additional assumption
    that the bound variables are disjoint from
    [rangeFreeVars] of the substitution.*)

Theorem fail_free_vars_SSubstAux:
(   forall (s : GSym G) (nt : Term s) (sub : SSubstitution vc),
    eqset 
        (tfreevars (tSSubstAux nt sub) vc)
        (   (diff (DeqVtype vc) (ALDom sub) (tfreevars nt vc)) 
            ++
              (rangeFreeVars 
                  (ALKeepFirst 
                        (DeqVtype vc) 
                         sub 
                         (tfreevars nt vc))
              )
         )
)
*
(   forall (s : GSym G) (pt : Pattern s) (sub : SSubstitution vc),
    eqset 
        (pfreevars (pSSubstAux pt sub) vc)
        ( (diff (DeqVtype vc) (ALDom sub) (pfreevars pt vc)) 
          ++
              (rangeFreeVars 
                  (ALKeepFirst 
                        (DeqVtype vc) 
                         sub 
                         (pfreevars pt vc))
)
         )
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l) 
    (llva : list (list (vType vc))) 
    (sub : SSubstitution vc),
    eqset 
        (mfreevars (mSSubstAux m llva sub) vc llva)
        ( (diff (DeqVtype vc) (ALDom sub) (mfreevars m vc llva)) 
           ++
              (rangeFreeVars 
                  (ALKeepFirst 
                        (DeqVtype vc) 
                         sub 
                         (mfreevars m vc llva))
              )
         )
).
Proof.
GInduction; allsimpl; introns Hyp; intros; cpx;
  try (simpl; rw diff_nil; rw ALKeepFirstNil; simpl;
      unfold rangeFreeVars, ALRange, ALKeepFirst; simpl;
      split;cpx);[| | | ].
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
- Case "tnode". rw <- lBoundVarsSameSSubstAux.
  apply Hyp.
- Case "mtcons". destruct llva as [| llh llva];
   simpl; cpx; unfold subtractv;
   allrw diff_app_r; allsimpl.
  + split. 
    * introv Hin; allrw in_app_iff;
      dorn Hin; try (apply Hyp0 in Hin);
      try (apply Hyp in Hin);
      try(rw in_app_iff in Hin); try(dorn Hin);cpx;
      try (apply in_diff in Hin); exrepnd; cpx;
      right;
      try (apply rangeFreeVarsKeepFirstAppL; cpx; fail);
      try (apply rangeFreeVarsKeepFirstAppR; cpx; fail).
    * introv Hin; allrw in_app_iff.
      dorn Hin;[dorn Hin;[left|right]|];
      try apply Hyp0;
      try apply Hyp;
      allrw in_app_iff; cpx;[].
      rw lin_flat_map in Hin. exrepnd.
      rw in_map_iff in Hin1. exrepnd.
      apply ALKeepFirstAppLin in Hin1.
      dorn Hin1;[left|right];
      try apply Hyp0;
      try apply Hyp;
      allrw in_app_iff; right; cpx;
      rw lin_flat_map; eexists; dands; eauto;
      rw in_map_iff; eexists; dands; eauto.

  + split. 
    * introv Hin. allrw in_app_iff.

      dorn Hin;[|apply Hyp0 in Hin; rw in_app_iff in Hin;
          dorn Hin; cpx;[];  
          right; apply rangeFreeVarsKeepFirstAppR; cpx].
      rw in_diff in Hin; exrepnd.
      apply Hyp in Hin0;
      allrw in_app_iff; exrepnd; dorn Hin0; cpx;[|].

      left. left. allrw in_diff; exrepnd; dands; cpx.
      introv Hc. apply Hin0. rw <- ALDomFilterCommute.
      apply in_diff. dands; cpx; fail.
      
      right. apply rangeFreeVarsKeepFirstAppL.
      rw lin_flat_map in Hin0.
      apply lin_flat_map.
      exrepnd. eexists; dands; eauto;[].
      rw in_map_iff in Hin0.
      apply in_map_iff.
      exrepnd. eexists; dands; eauto;[].
      apply ALKeepFirstLin.
      apply ALKeepFirstLin in Hin0.
      exrepnd.
      apply ALFindFilterSome in Hin3; dands; cpx;[].
      rw in_diff.
      dands; cpx.
    
    * introv Hin. allrw in_app_iff.

      dorn Hin;[dorn Hin|];[ | | ].

      left. allrw in_diff. exrepnd.
      dands; cpx;[].
      apply Hyp. allrw in_app_iff.
      left. allrw in_diff. exrepnd.
      dands; cpx;[].
      rw <- ALDomFilterCommute.
      rw in_diff. introv Hc.
      apply Hin. exrepnd. cpx; fail.

      allrw in_diff. right.
      exrepnd; cpx.
      apply Hyp0.
      allrw in_diff. allrw in_app_iff.
      allrw in_diff.
      left; cpx; fail.

      rw lin_flat_map in Hin. exrepnd.
      rw in_map_iff in Hin1. exrepnd.
      apply ALKeepFirstAppLin in Hin1.
      allsimpl. subst.

      exrepnd. left.
      allrw in_app_iff.
      allrw in_diff.
      dands; cpx.

      (** subgoal 2 is not provable.
          x is a free variable and is getting 
          captured by some bound variables in [llh].
            hence, the resultant
          set of free variables is
          incorrectly less *)

Abort.

Fixpoint trename_binders (G : CFGV)
  (gs : (GSym G)) (pt : Term gs) (vc : VarSym G) 
  (lva : list (vType vc)) {struct pt} :  Term gs :=
match pt in Term gs return Term gs with
| tleaf a b => tleaf a b 
| vleaf vcc var => vleaf vcc var  
| tnode p mix => tnode p (trename_binders  
                          mix
                          (lBoundVars (bndngPatIndices p) mix vc) 
                          lva) 
end
with prename_binders {G : CFGV}
  {gs : (GSym G)} (p : Pattern gs) (vc : VarSym G)
  (lva : list (vType vc)) {struct p} : Pattern gs  :=
match p with
| ptleaf a v => ptleaf a v
| pvleaf vcc var => pvleaf vcc var
(** patterns do not have internal bindings 
    (members of [PatProd] do not specify binding info).
   Hence the [nil] *)
| pnode p lpt => pnode p (mSSubstAux lpt [] sub)
| embed p nt => embed p (tSSubstAux nt sub)
end
with mSSubstAux (G : CFGV)
  (lgs : list (bool * GSym G)) (pts : Mixture lgs)
  (vc : VarSym G)
  (lbvars : list (list (vType vc)))
  (lva : SSubstitution vc)
  {struct pts}
      : Mixture lgs  := 
match pts in Mixture lgs return Mixture lgs with
| mnil  => mnil
(** the next case will never happen when called from [tSSubstAux]
    or  [pSSubstAux] *)
| mtcons _ _ ph ptl => 
    match lbvars with
    | [] => mtcons 
              (tSSubstAux ph sub) 
              (mSSubstAux ptl [] sub)
    | lh ::ltl => mtcons
                    (tSSubstAux ph (al_filter (DeqVtype vc) sub lh))
                    (mSSubstAux ptl ltl sub)
    end
| mpcons _ _ ph ptl =>
    match lbvars with
    | [] => mpcons 
              (pSSubstAux ph sub) 
              (mSSubstAux ptl [] sub)
    | lh ::ltl => mpcons
                    (pSSubstAux ph (al_filter (DeqVtype vc) sub lh))
                    (mSSubstAux ptl ltl sub)
    end
end.
*)
