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

Require Import Swap.
Require Import AssociationList.
Require Import Eqdep_dec.
(** printing #  $\times$ #×# *)
(** printing &  $\times$ #×# *)

Set Implicit Arguments.

Definition isReflSwapping {G : CFGV} {vc : VarSym G} (s : Swapping vc) :=
  ALDom s = ALRange s.

Lemma swapPreservesSize :forall  {G : CFGV} {vc : VarSym G} 
    (sw : Swapping vc),
     (  (forall (s : GSym G) (t : Term s),
            tSize (tSwap t sw) = tSize t )

         *
        (forall (s : GSym G) (pt : Pattern s),
            pSize (pSwap pt sw) = pSize pt)
         *
        (forall (l : @MixtureParam G) (m : Mixture l),
            mSize (mSwap m sw) = mSize m)).
Proof.
  intros. 
  GInduction; intros; allsimpl; auto.
Qed.

Hint Rewrite (fun G vc sw => (tcase (@swapPreservesSize G vc sw)))  : fast.
Hint Rewrite (fun G vc sw => (pcase (@swapPreservesSize G vc sw)))  : fast.
Hint Rewrite (fun G vc sw => (mcase (@swapPreservesSize G vc sw)))  : fast.

Lemma isReflSwapping_cons :
  forall {G} {vc : VarSym G} a b (s : Swapping vc),
    isReflSwapping ((a,b)::s) <=> a = b # isReflSwapping s.
Proof.
  unfold isReflSwapping; introv; simpl; split; intro k; cpx.
  repnd; allrw; sp.
Qed.




Lemma oneSwapVar_prop_s1 :
  forall {G : CFGV} {vc : VarSym G}
         (v a : vType vc),
    oneSwapVar v (a, a) = v.
Proof.
  introv.
  unfold oneSwapVar.
  ddeq; auto.
Qed.

Lemma swapVar_prop_s1 :
  forall {G : CFGV} {vc : VarSym G}
         (s : Swapping vc) (v : vType vc),
    isReflSwapping s
    -> swapVar s v = v.
Proof.
  induction s as [|x s]; introv isr; allsimpl; auto.
  destruct x as [a b].
  apply isReflSwapping_cons in isr; repnd; subst.
  rewrite oneSwapVar_prop_s1; sp.
Qed.

Lemma swap_prop_s1_aux :
  forall {G : CFGV} {vc : VarSym G},
    (forall (gs : GSym G) (t : Term gs) (s : Swapping vc),
       isReflSwapping s -> tSwap t s = t)
    *
    (forall (gs : GSym G) (p : Pattern gs) (s : Swapping vc),
       isReflSwapping s -> pSwap p s = p)
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) (s : Swapping vc),
       isReflSwapping s -> mSwap m s = m).
Proof.
  introv.
  apply GInduction; auto; introv.

  - intro isr; simpl.
    ddeq; auto.
    subst; simpl.
    rewrite swapVar_prop_s1; auto.

  - introv mix isr; simpl.
    rw mix; auto.

  - intro isr; simpl.
    destruct (DeqVarSym vc vc0); auto.
    subst; simpl.
    rewrite swapVar_prop_s1; auto.

  - introv tm isr; simpl.
    rw tm; auto.

  - introv mix isr; simpl.
    rw mix; auto.

  - introv tm mix isr; simpl.
    rw tm; auto.
    rw mix; auto.

  - introv pat tm isr; simpl.
    rw pat; auto.
    rw tm; auto.
Qed.

Hint Rewrite 
  (fun G vc gs t
    => (tcase (@swap_prop_s1_aux G  vc) gs t [] eq_refl)): fast.

Hint Rewrite 
  (fun G vc gs t
    => (pcase (@swap_prop_s1_aux G  vc) gs t [] eq_refl)): fast.

Hint Rewrite 
  (fun G vc gs t
    => (mcase (@swap_prop_s1_aux G  vc) gs t [] eq_refl)): fast.

Lemma swap_prop_s1 :
  forall {G : CFGV} {vc : VarSym G},
    (forall (gs : GSym G) (t : Term gs) (a : vType vc),
       tSwap t [(a,a)] = t)
    *
    (forall (gs : GSym G) (p : Pattern gs) (a : vType vc),
       pSwap p [(a,a)] = p)
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) (a : vType vc),
       mSwap m [(a,a)] = m).
Proof.
  introv.
  pose proof (@swap_prop_s1_aux G vc) as h; repnd.
  dands; introv.
  - apply h1; sp.
  - apply h0; sp.
  - apply h; sp.
Qed.

Lemma swapVar_S2 : forall {G : CFGV} {vc : VarSym G}
(v a a' : vType vc),
swapVar [(a,a'),(a,a')] v = v.
Proof.
intros. simpl.
    ddeq; subst; auto; tcsp.
Qed.

Lemma swapVar_S2app : forall {G : CFGV} {vc : VarSym G}
  (sh :vType vc * vType vc)
  (v : vType vc),
swapVar ([sh] ++ [sh]) v  = v.
Proof.
intros. destruct sh. simpl. simpl.
    ddeq; subst; auto; tcsp.
Qed.

(* stronger version below
Lemma swap_prop_s2 :
  forall {G : CFGV} {vc : VarSym G},
    (forall (gs : GSym G) (t : Term gs) (a a' : vType vc),
       tSwap t [(a,a'),(a,a')] = t)
    *
    (forall (gs : GSym G) (p : Pattern gs) (a a' : vType vc),
       pSwap p [(a,a'),(a,a')] = p)
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) (a a' : vType vc),
       mSwap m [(a,a'),(a,a')] = m).
Proof.
  introv.
  apply GInduction; auto; introv.

  - simpl; ddeq; auto.
    subst; simpl.
    ddeq; subst; auto; tcsp.

  - introv mix; introv; simpl.
    rw mix; auto.

  - simpl; ddeq; auto.
    subst; simpl; ddeq; subst; tcsp.

  - introv tm; introv; simpl.
    rw tm; auto.

  - introv mix; introv; simpl.
    rw mix; auto.

  - introv tm mix; introv; simpl.
    rw mix; rw tm; auto.

  - introv pat tm; introv; simpl.
    rw pat; rw tm; auto.
Qed.
*)

Lemma swap_prop_s3 :
  forall {G : CFGV} {vc : VarSym G}
         (a a' : vType vc),
    (tSwap (vleaf vc a) [(a,a')] = vleaf vc a')
    *
    (pSwap (pvleaf vc a) [(a,a')] = pvleaf vc a').
Proof.
  introv; simpl; DDeqs; sp.
Qed.

Lemma swapVar_app :
  forall {G : CFGV} {vc : VarSym G}
         (s1 s2 : Swapping vc) (v : vType vc),
    swapVar s2 (swapVar s1 v) = swapVar (s1 ++ s2) v.
Proof.
  induction s1 as [|x s1]; introv; simpl; sp.
Qed.

Lemma swapVar_s2stronger :
  forall {G : CFGV} {vc : VarSym G}
         (sw : Swapping vc) (v : vType vc),
    swapVar ((rev sw)++sw) v = v.
Proof.
  intros G vc sw. induction sw as [|sh sw].
  - intros. simpl. trivial.
  - intros. simpl. rw <- app_assoc.
    rw (cons_as_app _ sh sw).
    rewrite <- swapVar_app.
    rewrite <- swapVar_app.
    rewrite <- swapVar_app.
    remember (swapVar (rev sw) v) as sv.
    rewrite  (swapVar_app [sh] [sh]).
    rewrite  swapVar_S2app.
    subst.
    rewrite  swapVar_app.
    trivial.
Qed.

Lemma swapVar_s2stronger2 :
  forall {G : CFGV} {vc : VarSym G}
         (sw : Swapping vc) (v : vType vc),
    swapVar (sw++(rev sw)) v = v.
Proof.
  intros.
  remember (rev sw) as rsw.
  rewrite <- rev_involutive with (l:=sw).
  subst.
  apply swapVar_s2stronger.
Qed.


Lemma LInEquivariant : forall {G : CFGV} {vc : VarSym G},
  @EquiVariantRel G vc _ _
   (fun x s => swapVar s x) 
    (fun x s => swapLVar s x) (LIn).
Proof.
  unfold EquiVariantRel.
  intros.
  induction tb; cpx.
  allsimpl.
  dorn X;[left; subst | right]; cpx.
Qed.

Lemma swapVarInj:
  forall {G : CFGV} {vc : VarSym G}
         (sw : Swapping vc) (va vb : vType vc),
    swapVar sw va = swapVar sw vb
    -> va = vb.
Proof.
  induction sw.
  - simpl. auto.
  - simpl. introv Heq. apply IHsw in Heq.
    destruct a.
    allsimpl. revert Heq.
    cases_ifd Hda; cases_ifd Hdb; subst; cpx;
    cases_ifd Hdc; try cases_ifd Hdd; intros; subst; cpx.
Qed.

Lemma NegLInEquivariant : forall {G : CFGV} {vc : VarSym G},
  @EquiVariantRel G vc _ _
   (fun x s => swapVar s x) 
    (fun x s => swapLVar s x) (fun x l => !LIn x l).
Proof.
  unfold EquiVariantRel.
  intros.
  induction tb; cpx.
  allsimpl. introv Hc.
  apply H.
  dorn Hc;[left; subst | right]; cpx.
  - apply swapVarInj in Hc; trivial.
  - apply IHtb in Hc; cpx.
Qed.

Lemma DisjointEquivariant : forall {G : CFGV} {vc : VarSym G},
  @EquiVariantRelSame G vc _
    (fun x s => swapLVar s x) (disjoint).
Proof.
  unfold EquiVariantRelSame, EquiVariantRel.
  intros.
  induction ta; cpx.
  allsimpl. introv Hin Hinc.
  allsimpl.
  dorn Hin.
  - revert Hinc. subst. apply NegLInEquivariant.
    introv Hc. repeat (disjoint_reasoning).
  - repeat (disjoint_reasoning).
    disjoint_lin_contra.
Qed.

Lemma NoRepeatsEquivariant : forall {G : CFGV} {vc : VarSym G},
  @EquiVariantRelUn G vc _
    (fun x s => swapLVar s x) (no_repeats).
Proof.
  unfold EquiVariantRelUn.
  introv X. intros.
  induction ta; cpx.
  inverts X.
  allsimpl. constructor; cpx.
  apply NegLInEquivariant. trivial.
Qed.

Lemma AllVarsEquivariant : 
  forall {G : CFGV} {vc : VarSym G},
    (forall (gs : GSym G), 
    EquiVariantFn (@tSwap _ vc gs)
                  (fun x s => swapLVar s x) 
                  (tAllVars ))
    *
    (forall (gs : GSym G),
    EquiVariantFn (@pSwap _ vc gs)
                  (fun x s => swapLVar s x) 
                  (pAllVars ))
    *
    (forall (lgs : list (bool * GSym G)),
     EquiVariantFn (@mSwap _ vc lgs)
                (fun x s => swapLVar s x) 
                (mAllVars )).
Proof.
  introv.
  GInduction; auto; introns Hyp; intros; allsimpl ; auto.

  - simpl. rewrite DeqSym. symmetry. rewrite DeqSym.
    destruct_head_match; try subst;  cpx.

  - simpl. rewrite DeqSym. symmetry. rewrite DeqSym.
    destruct_head_match; try subst;  cpx.

  - unfold swapLVar. rw map_app.
    unfold swapLVar in Hyp0. 
    unfold swapLVar in Hyp. 
    f_equal; cpx.
    
  - unfold swapLVar. rw map_app.
    unfold swapLVar in Hyp0. 
    unfold swapLVar in Hyp. 
    f_equal; cpx.
Qed.

Lemma bndngVarsDeepEquivariant : 
  forall {G : CFGV} {vc : VarSym G},
    (forall (gs : GSym G), 
    EquiVariantFn (@tSwap _ vc gs)
                  (fun x s => swapLVar s x) 
                  (tBndngVarsDeep vc))
    *
    (forall (gs : GSym G),
    EquiVariantFn (@pSwap _ vc gs)
                  (fun x s => swapLVar s x) 
                  (pBndngVarsDeep vc ))
    *
    (forall (lgs : list (bool * GSym G)),
     EquiVariantFn (@mSwap _ vc lgs)
                (fun x s => swapLVar s x) 
                (mBndngVarsDeep vc )).
Proof.
  introv.
  GInduction; auto; introns Hyp; intros; allsimpl ; auto.

  - Case "pvleaf".
    simpl. rewrite DeqSym. symmetry. rewrite DeqSym.
    destruct_head_match; try subst;  cpx.


  - Case "mtcons". unfold swapLVar. rw map_app.
    unfold swapLVar in Hyp0. 
    unfold swapLVar in Hyp. 
    f_equal; cpx.
    
  - Case "mpcons". unfold swapLVar. rw map_app.
    unfold swapLVar in Hyp0. 
    unfold swapLVar in Hyp. 
    f_equal; cpx.
Qed.


Lemma swapLVar_app :
  forall  {G : CFGV} {vc : VarSym G} s vs1 vs2, 
    @swapLVar G vc s (vs1 ++ vs2) = swapLVar s vs1 ++ swapLVar s vs2.
Proof.
  introv.
  unfold swapLVar.
  rw map_app; auto.
Qed.

Lemma pBndngVars_swap : forall {G : CFGV} {vc : VarSym G},
  (
    (forall (gs : GSym G) (t : Term gs), True)
    *
    (forall (g : GSym G) (ph : Pattern g) s,
       pBndngVars vc (pSwap ph s)
       = swapLVar s (pBndngVars vc ph))
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) s,
       mBndngVars vc (mSwap m s)
       = swapLVar s (mBndngVars vc m))
  ).
Proof. intros.
  GInduction; auto; introv; allsimpl; DDeqs; auto.
  introv P M; introv.
  rewrite swapLVar_app.
  apply app_if; auto.
Qed.

Lemma getBVarsNth_swap :
  forall {G : CFGV} {vc : VarSym G} 
    (p : MixtureParam) (m : Mixture p) x s,
    getBVarsNth vc (mSwap m s) x
    = swapLVar s (getBVarsNth vc m x).
Proof.
  induction m; introv; simpl; auto;
  destruct x; simpl; auto.
  apply (snd (fst pBndngVars_swap)).
Qed.

Lemma swapLVar_flat_map :
  forall {G : CFGV} {vc : VarSym G} A s f (l : list A),
    @swapLVar G vc s (flat_map f l) = flat_map (compose (swapLVar s) f) l.
Proof.
  unfold swapLVar.
  introv.
  rw map_flat_map; sp.
Qed.

Lemma lBoundVars_swap :
  forall {G : CFGV} {vc : VarSym G}
    (lgs : list (bool * GSym G)) (m : Mixture lgs) bsl s,
    lBoundVars vc bsl (mSwap m s)
    = swapLLVar s (lBoundVars vc bsl m).
Proof.
  induction bsl; simpl; auto; introv.
  rw IHbsl.
  apply eq_cons; auto.
  rewrite swapLVar_flat_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x; simpl; auto; apply getBVarsNth_swap.
Qed.

Lemma lBoundVars_equivariant :
  forall  {G : CFGV} {vc : VarSym G} 
    (lgs : list (bool * GSym G)) bsl,
    EquiVariantFn
      (fun m s => mSwap m s)
      (fun l s => swapLLVar s l)
      (@lBoundVars G vc lgs bsl).
Proof.
  intros.
  unfold EquiVariantFn; introv.
  rewrite lBoundVars_swap; auto.
Qed.

Lemma injective_fun_swapVar :
  forall {G : CFGV} {vc : VarSym G}
   s, injective_fun (@swapVar G vc s).
Proof.
  unfold swapVar, injective_fun.
  induction s; simpl; auto.
  introv k.
  apply IHs in k.
  destruct a.
  unfold oneSwapVar in k.
  ddeq; subst; sp.
Qed.

Hint Immediate injective_fun_swapVar.
(** !! rename it to subtractEquivariant *)
Lemma swapLVar_subtractv :
  forall {G : CFGV} {vc : VarSym G} s l1 l2,
    @swapLVar G vc s (subtractv l1 l2) = subtractv (swapLVar s l1) (swapLVar s l2).
Proof.
  introv.
  unfold swapLVar, subtractv.
  apply map_diff_commute; auto.
Qed.

Lemma lheadEquivariant :
   forall {G : CFGV} {vc : VarSym G},
    @EquiVariantFn G vc _ _
                   (fun x s => swapLLVar s x) 
                   (fun x s => swapLVar s x) 
                   (lhead).
Proof.
  intros. unfolds_base.
  intros. destruct ta; cpx.
Qed.

Lemma tailEquivariant :
   forall {G : CFGV} {vc : VarSym G},
    @EquiVariantFn G vc _ _
                   (fun x s => swapLLVar s x) 
                   (fun x s => swapLLVar s x) 
                   (@tail _).
Proof.
  intros. unfolds_base.
  intros. destruct ta; cpx.
Qed.

   
Lemma freevarsEquivariant : 
  forall {G : CFGV} {vc : VarSym G},
    (forall (gs : GSym G), 
    EquiVariantFn (@tSwap _ vc gs)
                  (fun x s => swapLVar s x) 
                  (tfreevars vc))
    *
    (forall (gs : GSym G),
    EquiVariantFn (@pSwap _ vc gs)
                  (fun x s => swapLVar s x) 
                  (pfreevars vc ))
    *
    (forall (lgs : list (bool * GSym G)),
    EquiVariantFn2 (@mSwap _ vc lgs)
                   (fun x s => swapLLVar s x) 
                   (fun x s => swapLVar s x) 
                   (@mfreevars _ _ _)).
Proof.
  introv.
  GInduction; auto; introns Hyp; intros; allsimpl ; auto.

  - Case "vleaf".
    simpl. rewrite DeqSym. symmetry. rewrite DeqSym.
    destruct_head_match; try subst;  cpx.

  - Case "tnode".
    unfold allBndngVars.
    rewrite <- (lBoundVars_equivariant).
    cpx.

  - Case "pnode".
    rewrite Hyp. simpl.
    refl.
    
  - Case "mtcons".
    rewrite <- Hyp. 
    rewrite <- lheadEquivariant.
    rewrite <- swapLVar_subtractv.
    rewrite swapLVar_app. f_equal; cpx.
    rewrite <- tailEquivariant.
    cpx.

  - Case "mpcons".
    rewrite <- Hyp. 
    rewrite <- lheadEquivariant.
    rewrite <- swapLVar_subtractv.
    rewrite swapLVar_app. f_equal; cpx.
    rewrite <- tailEquivariant.
    cpx.
Qed.

Lemma swap_prop_s2Stronger :
  forall {G : CFGV} {vc : VarSym G},
    (forall (gs : GSym G) (t : Term gs) (sw : Swapping vc),
       tSwap t (sw ++ (rev sw)) = t)
    *
    (forall (gs : GSym G) (p : Pattern gs) (sw : Swapping vc),
       pSwap p (sw ++ (rev sw)) = p)
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) 
      (sw : Swapping vc),
       mSwap m (sw ++ (rev sw)) = m).
Proof.
  introv.
  GInduction; auto; introv; allsimpl ; cpx.

  - simpl; ddeq; auto. subst.
    simpl. f_equal.
    apply swapVar_s2stronger2.

  - introv mix; introv; simpl.
    rw mix; auto.

  - simpl; ddeq; auto. subst.
    simpl. f_equal.
    apply swapVar_s2stronger2.

  - introv tm; introv; simpl.
    rw tm; auto.

  - introv mix; introv; simpl.
    rw mix; auto.

  - introv tm mix; introv; simpl.
    rw mix; rw tm; auto.

  - introv pat tm; introv; simpl.
    rw pat; rw tm; auto.
Qed.

Hint Rewrite (fun G vc 
    => tcase (@swap_prop_s2Stronger G vc)) : fast.
Hint Rewrite (fun G vc 
    => pcase (@swap_prop_s2Stronger G vc)) : fast.
Hint Rewrite (fun G vc 
    => mcase (@swap_prop_s2Stronger G vc)) : fast.
Hint Rewrite (fun G vc 
    => (@swapVar_s2stronger2 G vc)) : fast.

Lemma swapVar_e1stronger :
  forall {G : CFGV} {vc : VarSym G}
         (swa swb : Swapping vc) (v : vType vc),
    swapVar (swa ++ swb) v = swapVar (swb ++ (swapSwap swb swa)) v.
Proof.
  intros G vc sw. induction sw as [|sh sw].
  - intros. simpl. autorewrite with fast. trivial.
  - intros. rw cons_as_app. rw <- app_assoc.
    simpl. rw IHsw.
    rewrite <- swapVar_app.
    rw cons_as_app. rw  app_assoc.
    rewrite <- swapVar_app.
    f_equal. 
    destruct sh as [sl sr].
    simpl.
    cases_ifd Hd; subst; auto.
    + rewrite <- swapVar_app.
      simpl.
      ddeq; auto.
      cpx.
    + ddeq; subst; auto.
      * rewrite <- swapVar_app.
        simpl. ddeq; auto.
        cpx.
      * rewrite <- swapVar_app.
        simpl. ddeq; auto;
        cpx;
        apply swapVarInj in e; subst; cpx.
Qed.

Lemma swap_app :
  forall {G : CFGV} {vc : VarSym G},
    (forall (gs : GSym G) (t : Term gs) (s1 s2 : Swapping vc),
       tSwap (tSwap t s1) s2 = tSwap t (s1 ++ s2))
    *
    (forall (gs : GSym G) (p : Pattern gs) (s1 s2 : Swapping vc),
       pSwap (pSwap p s1) s2 = pSwap p (s1 ++ s2))
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) (s1 s2 : Swapping vc),
       mSwap (mSwap m s1) s2 = mSwap m (s1 ++ s2)).
Proof.
  introv.
  apply GInduction; auto; introv.

  - simpl.
    ddeq; auto.
    subst; simpl.
    rewrite swapVar_app; auto.

  - introv mix; introv; simpl.
    rw mix; auto.

  - simpl.
    ddeq; auto; subst; simpl.
    rewrite swapVar_app; auto.

  - introv tm; introv; simpl.
    rw tm; auto.

  - introv mix; introv; simpl.
    rw mix; auto.

  - introv tm mix; introv; simpl.
    rw tm; auto.
    rw mix; auto.

  - introv pat tm; introv; simpl.
    rw pat; auto.
    rw tm; auto.
Qed.

Hint Rewrite (fun G vc => tcase (@swap_app G vc)) : SwapAppR.
Hint Rewrite (fun G vc => pcase (@swap_app G vc)) : SwapAppR.
Hint Rewrite (fun G vc => mcase (@swap_app G vc)) : SwapAppR.

Hint Rewrite <- (fun G vc => tcase (@swap_app G vc)) : SwapAppL.
Hint Rewrite <- (fun G vc => pcase (@swap_app G vc)) : SwapAppL.
Hint Rewrite <- (fun G vc => mcase (@swap_app G vc)) : SwapAppL.

Hint Rewrite (fun G vc =>  (@swapVar_app G vc)) : SwapAppR.
Hint Rewrite <- (fun G vc =>  (@swapVar_app G vc)) : SwapAppL.

(* stronger version below
Lemma swap_prop_e1 :
  forall {G : CFGV} {vc : VarSym G},
    (forall (gs : GSym G) (t : Term gs) (a a' b b' : vType vc),
       tSwap t [(b,b'),(a,a')]
       = tSwap t [(a,a'),(oneSwapVar b (a,a'),oneSwapVar b' (a,a'))])
    *
    (forall (gs : GSym G) (p : Pattern gs) (a a' b b' : vType vc),
       pSwap p [(b,b'),(a,a')]
       = pSwap p [(a,a'),(oneSwapVar b (a,a'),oneSwapVar b' (a,a'))])
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) (a a' b b' : vType vc),
       mSwap m [(b,b'),(a,a')]
       = mSwap m [(a,a'),(oneSwapVar b (a,a'),oneSwapVar b' (a,a'))]).
Proof.
  introv.
  apply GInduction; auto; introv.

  - simpl; ddeq; auto; subst; tcsp; simpl; ddeq; try subst; tcsp.

  - introv mix; introv; simpl.
    rw mix; simpl; auto.

  - simpl; ddeq; auto; subst; simpl; ddeq; try subst; tcsp.

  - introv tm; introv; simpl.
    rw tm; simpl; auto.

  - introv mix; introv; simpl.
    rw mix; simpl; auto.

  - introv tm mix; introv; simpl.
    rw mix; rw tm; simpl; auto.

  - introv pat tm; introv; simpl.
    rw pat; rw tm; simpl; auto.
Qed.
*)

Lemma swap_prop_e1Stronger :
  forall {G : CFGV} {vc : VarSym G},
    (forall (gs : GSym G) (t : Term gs) (swa swb : Swapping vc),
       tSwap t (swa ++ swb) = tSwap t (swb ++ (swapSwap swb swa)))
    *
    (forall (gs : GSym G) (t : Pattern gs) (swa swb : Swapping vc),
       pSwap t (swa ++ swb) = pSwap t (swb ++ (swapSwap swb swa)))
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) 
      (swa swb : Swapping vc),
       mSwap m (swa ++ swb) = mSwap m (swb ++ (swapSwap swb swa))).
Proof.
  introv.
  apply GInduction; auto; introv.

  - simpl. f_equal. destruct_head_match; auto.
    subst. simpl. apply swapVar_e1stronger.

  - introv mix; introv; simpl.
    rw mix; simpl; auto.

  - simpl. f_equal. destruct_head_match; auto.
    subst. simpl. apply swapVar_e1stronger.

  - introv tm; introv; simpl.
    rw tm; simpl; auto.

  - introv mix; introv; simpl.
    rw mix; simpl; auto.

  - introv tm mix; introv; simpl.
    rw mix; rw tm; simpl; auto.

  - introv pat tm; introv; simpl.
    rw pat; rw tm; simpl; auto.
Qed.

Section SwapProps.
Context {G : CFGV} {vc : VarSym G}.
Notation vcType := (vType vc).

Lemma swapVarImplies :
  forall (sw : Swapping vc) v w,
         w = swapVar sw v
         -> w = v [+] LIn w (ALDom sw) [+] LIn w (ALRange sw).
Proof.
  simpl; induction sw as [| s sw IHvs1]; introv Heq; cpx.
  destruct s as [va vb].
  allsimpl. apply IHvs1 in Heq.
  ddeq; sp; try subst; cpx.
Qed.

Lemma swapvarImplies2 :
  forall (vs1 vs2 : list vcType),
    length vs1 = length vs2
    -> forall v,
         let w := swapVar (combine vs1 vs2) v in
         w = v [+] LIn w vs1 [+] LIn w vs2.
Proof.
  simpl; induction vs1 as [| va vs1 IHvs1]; 
    introv len; introv; allsimpl; destruct vs2 as [|vb vs2]; allsimpl; cpx.
  ddeq; sp; subst.
  - pose proof (IHvs1 vs2 len vb) as h; sp.
  - pose proof (IHvs1 vs2 len va) as h; sp.
  - pose proof (IHvs1 vs2 len v) as h; sp.
Qed.

Lemma swapVarNoChange2 :
  forall v (vsa vsb : list vcType),
    !LIn v vsa
    -> !LIn v vsb
    -> swapVar (combine vsa vsb) v = v.
Proof.
  induction vsa; simpl; introv ni1 ni2; auto.
  allrw not_over_or; repnd.
  destruct vsb; simpl; auto.
  allsimpl; allrw not_over_or; repnd.
  ddeq; sp.
Qed.

Lemma swapVarNoChange :
  forall v (sw : Swapping vc),
    !LIn v (ALDom sw)
    -> !LIn v (ALRange sw)
    -> swapVar sw v = v.
Proof.
  induction sw; simpl; introv ni1 ni2; auto.
  allrw not_over_or; repnd.
  allsimpl.
  ddeq; try subst; sp.
Qed.

Lemma swapVarDisjChain : forall
  (vsa vs vsb : list (vType vc))
  (v : vType vc),
    length vs = length vsa
    -> length vs = length vsb
    -> no_repeats vs
    -> no_repeats vsb
    -> disjoint vs (vsa ++ vsb ++ [v])
    -> disjoint vsb (vsa ++ [v])
    -> swapVar ((combine vsa  vs) ++  (combine vs  vsb)) v
       = swapVar (combine vsa  vsb) v.
Proof.
  induction vsa; introv lena lenb norepa norepb disja disjb;
  allsimpl; destruct vs; allsimpl; cpx;
  destruct vsb; allsimpl; cpx.

  allrw disjoint_cons_l; allrw disjoint_cons_r;
  allrw disjoint_app_r;  allrw disjoint_cons_r;
  allrw disjoint_app_r;  allrw disjoint_singleton_r;
  allsimpl; allrw in_app_iff; allsimpl; allrw in_app_iff;
  allrw in_single_iff; allrw not_over_or;
  allrw no_repeats_cons; repnd; GC.
  ddeq; subst;try (complete cpx);[|].

  - rewrite <- swapVar_app. simpl.
    ddeq; try subst;try (complete cpx);[| | ].

    + repeat (rw swapVarNoChange2; auto).

    + provefalse. apply n.
      rw swapVarNoChange2; auto.

    + repeat (rw swapVarNoChange2; auto).
      repeat (rw swapVarNoChange2 in n; auto).
      cpx.

  - rewrite <- swapVar_app. simpl.
    ddeq; try subst;try (complete cpx);[| | ].

    + symmetry in lena.
      pose proof (swapvarImplies2 vsa vs lena v) as o;
      simpl in o. sp.

    + symmetry in lena.
      pose proof (swapvarImplies2 vsa vs lena v) as o;
       simpl in o;  sp.

    + pose proof (@in_deq vcType (DeqVtype vc) v vsa) as h.
      dorn h; try (complete (repeat (rw swapVarNoChange2; auto)));[].
      rewrite swapVar_app.
      apply IHvsa; auto; allrw disjoint_app_r; allrw disjoint_singleton_r; auto.
Qed.

Lemma swapDisjChain : forall
  (vsa vs vsb : list vcType),
    length vs = length vsa
    -> length vs = length vsb
    -> no_repeats vs
    -> no_repeats vsb
    -> 
  (forall (gs : GSym G) (t : Term gs),
       disjoint vs (vsa ++ vsb ++ (tAllVars t))
       -> disjoint vsb (vsa ++ tAllVars t)
       -> tSwap t ((combine vsa  vs) ++  (combine vs  vsb))
            = tSwap t (combine vsa  vsb))
  *
  (forall (gs : GSym G) (t : Pattern gs),
       disjoint vs (vsa ++ vsb ++ (pAllVars t))
       -> disjoint vsb (vsa ++ pAllVars t)
       -> pSwap t ((combine vsa  vs) ++  (combine vs  vsb))
            = pSwap t (combine vsa  vsb))

    *
  (forall (lgs : MixtureParam) (m : Mixture lgs) ,
       disjoint vs (vsa ++ vsb ++ (mAllVars m))
       -> disjoint vsb (vsa ++ mAllVars m)
       -> mSwap m ((combine vsa  vs) ++  (combine vs  vsb))
            = mSwap m (combine vsa  vsb)).
Proof.
  introv Hlena Hlenb Hnr Hnrb.
  apply GInduction; auto; introns Hdis; allsimpl.

  - Case "vleaf". simpl. f_equal. rewrite DeqSym. symmetry.  rewrite DeqSym.
    destruct_head_match; cpx.
    subst.
    simpl. symmetry. apply swapVarDisjChain; auto;
    repeat(disjoint_reasoning); allsimpl;
    allrewrite (@DeqTrue (VarSym G)); allsimpl;
    repeat(disjoint_reasoning).

  - Case "pnode".
    rw Hdis; simpl; auto.

  - Case "pvleaf". simpl. f_equal. rewrite DeqSym. symmetry.  rewrite DeqSym.
    destruct_head_match; cpx.
    subst.
    simpl. symmetry. apply swapVarDisjChain; auto;
    repeat(disjoint_reasoning); allsimpl;
    allrewrite (@DeqTrue (VarSym G)); allsimpl;
    repeat(disjoint_reasoning).

  - rw Hdis; simpl; auto.
  - rw Hdis; simpl; auto.
  - f_equal.
    + apply Hdis; repeat(disjoint_reasoning).
    + apply Hdis0; repeat(disjoint_reasoning).

  - f_equal.
    + apply Hdis; repeat(disjoint_reasoning).
    + apply Hdis0; repeat(disjoint_reasoning).
Qed.

Lemma swapVarSwitch : forall
    (sw : Swapping vc) 
    (v : vType vc),
    swapVar sw v = swapVar (ALSwitch sw) v.
Proof.
  induction sw as [|(l,r) sw Hind]; auto;[].
  intros. simpl.
  ddeq; subst; cpx.
  subst r. cpx.
Qed.
Lemma swapSwitch :
    (forall (gs : GSym G) (t : Term gs) (sw : Swapping vc),
       tSwap t sw = tSwap t (ALSwitch sw))
    *
    (forall (gs : GSym G) (p : Pattern gs) (sw : Swapping vc),
       pSwap p sw = pSwap p(ALSwitch sw))
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) 
      (sw : Swapping vc),
       mSwap m sw = mSwap m (ALSwitch sw)).
Proof.
  introv.
  GInduction; auto; introv; allsimpl ; cpx.

  - simpl. f_equal.
    rewrite DeqSym. symmetry. rewrite DeqSym. symmetry.
    ddeq; auto. subst.
    simpl. apply swapVarSwitch.

  - introv mix; introv; simpl.
    rw mix; auto.

  - simpl. f_equal.
    rewrite DeqSym. symmetry. rewrite DeqSym. symmetry.
    ddeq; auto. subst.
    simpl. apply swapVarSwitch.

  - introv tm; introv; simpl.
    rw tm; auto.

  - introv mix; introv; simpl.
    rw mix; auto.

  - introv tm mix; introv; simpl.
    rw mix; rw tm; auto.

  - introv pat tm; introv; simpl.
    rw pat; rw tm; auto.
Qed.


Lemma swapVarRevNoRep : forall
    (sw : Swapping vc) 
    (v : vType vc),
    no_repeats (ALDom sw)
    -> no_repeats (ALRange sw) 
    -> disjoint (ALDom sw) (ALRange sw) 
    -> swapVar sw v = swapVar (rev sw) v.
Proof.
  induction sw as [|(l,r) sw Hind]; auto;[].
  introv H1nr H2nr Hdis. allsimpl.
  allrw disjoint_cons_l; allrw disjoint_cons_r;
  allrw disjoint_app_r;  allrw disjoint_cons_r;
  allrw disjoint_app_r;  allrw disjoint_singleton_r;
  allsimpl; allrw in_app_iff; allsimpl; allrw in_app_iff;
  allrw in_single_iff; allrw not_over_or;
  allrw no_repeats_cons; repnd; GC.
  assert (!LIn l (ALDom (rev sw))) by
    (allunfold ALDom; introv Hc;
    eauto 3 with SetReasoning).
    assert (!LIn r (ALDom (rev sw))) by 
      (allunfold ALDom; introv Hc;
      eauto 3 with SetReasoning).
    assert (!LIn l (ALRange (rev sw))) by
      (allunfold ALRange; introv Hc;
      eauto 3 with SetReasoning).
    assert (!LIn r (ALRange (rev sw))) by
      (allunfold ALRange; introv Hc;
      eauto 3 with SetReasoning).
  ddeq; try subst; cpx.
  - 
    rw Hind; auto.
    rewrite <- swapVar_app. simpl.
    ddeq; try (subst; cpx; fail).
    + rewrite swapVarNoChange; cpx.
    + rewrite swapVarNoChange in n; cpx.
    + rewrite swapVarNoChange in n; cpx.

  - 
    rw Hind; auto.
    rewrite <- swapVar_app. simpl.
    ddeq; try (subst; cpx; fail).
    + applysym swapVarImplies in e. cpx.
    + rewrite swapVarNoChange; cpx.
    + rewrite swapVarNoChange in n1; cpx.

  - 
    rw Hind; auto.
    rewrite <- swapVar_app. simpl.
    ddeq; try (subst; cpx; fail).
    + applysym swapVarImplies in e. cpx.
    + applysym swapVarImplies in e. cpx.
Qed.
  
Lemma swapRevNoRep :
    (forall (gs : GSym G) (t : Term gs) (sw : Swapping vc),
      no_repeats (ALDom sw)
      -> no_repeats (ALRange sw) 
      -> disjoint (ALDom sw) (ALRange sw)        
      -> tSwap t sw = tSwap t (rev sw))
    *
    (forall (gs : GSym G) (p : Pattern gs) (sw : Swapping vc),
      no_repeats (ALDom sw)
      -> no_repeats (ALRange sw) 
      -> disjoint (ALDom sw) (ALRange sw)        
       -> pSwap p sw = pSwap p(rev sw))
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) 
      (sw : Swapping vc),
      no_repeats (ALDom sw)
      -> no_repeats (ALRange sw) 
      -> disjoint (ALDom sw) (ALRange sw)        
       -> mSwap m sw = mSwap m (rev sw)).
Proof.
  introv.
  GInduction; auto; introv; allsimpl ; introns Hyp; allsimpl; cpx.

  - simpl. f_equal.
    rewrite DeqSym. symmetry. rewrite DeqSym. symmetry.
    ddeq; auto. subst.
    simpl. apply swapVarRevNoRep; auto.

  - rw Hyp; auto.

  - simpl. f_equal.
    rewrite DeqSym. symmetry. rewrite DeqSym. symmetry.
    ddeq; auto. subst.
    simpl. apply swapVarRevNoRep; auto.

  - rw Hyp; auto.
  - rw Hyp; auto.
  - rw Hyp; auto. rw Hyp0; auto.
  - rw Hyp; auto. rw Hyp0; auto.
Qed.

Lemma swapVarIn : forall (sw : Swapping vc) v,
    LIn v (ALDom sw)
    -> !LIn v (ALRange sw)
    -> no_repeats (ALRange sw)
    -> disjoint (ALDom sw) (ALRange sw)
    -> LIn (swapVar sw v) (ALRange sw).
Proof.
  induction sw; simpl; introv i1 ni2 norep disj; auto; try (complete sp).
  allrw disjoint_cons_l; allrw disjoint_cons_r; repnd; allsimpl.
  allrw not_over_or; repnd.
  allrw no_repeats_cons; repnd.
  ddeq; try (complete sp);[].
  rw swapVarNoChange; auto.
Qed.

Lemma swapVarInOrEq : forall (sw : Swapping vc) v,
    !LIn v (ALRange sw)
    -> no_repeats (ALRange sw)
    -> disjoint (ALDom sw) (ALRange sw)
    -> (LIn (swapVar sw v) (ALRange sw) [+] (swapVar sw v =v )).
Proof.
  intros.
  destruct (in_deq _ (DeqVtype vc) v (ALDom sw));[left | right].
  - apply swapVarIn; auto.
  - apply swapVarNoChange; cpx.
Qed.

Lemma swapVarInOrEq2 : forall (sw : Swapping vc) v,
    !LIn v (ALRange sw)
    -> no_repeats (ALRange sw)
    -> disjoint (ALDom sw) (ALRange sw)
    -> ((LIn (swapVar sw v) (ALRange sw) # LIn v (ALDom sw))
        [+] ((swapVar sw v =v ) 
              # (!LIn v (ALDom sw)))).
Proof.
  intros.
  destruct (in_deq _ (DeqVtype vc) v (ALDom sw));[left | right].
  - dands; auto. apply swapVarIn; auto.
  -   dands; auto.
    apply swapVarNoChange; cpx.
Qed.

Lemma swapLVarDisjoint: forall (sw : Swapping vc) lv,
  disjoint lv (ALRange sw)
  -> no_repeats (ALRange sw)
  -> disjoint (ALDom sw) (ALRange sw)
  -> disjoint (swapLVar sw lv) (ALDom sw).
Proof.
  induction lv; cpx.
  allsimpl.
  introv Hdis Hnt H2dis.
  apply disjoint_cons_l in Hdis.
  repnd. apply disjoint_cons_l.
  applydup IHlv in H2dis; cpx.
  dands; cpx.
  applydup swapVarInOrEq2 in Hdis; cpx;[].
  repeat(in_reasoning); repnd; try subst; cpx.
  - introv Hin. disjoint_lin_contra.
  - rewrite Hdis2. sp.
Qed.

Lemma swapLVarDisjoint2: forall (swl swr lv: list (vType vc)),
  disjoint lv swr
  -> length swl = length swr
  -> no_repeats swr
  -> disjoint swl swr
  -> disjoint (swapLVar (combine swl swr) lv) swl.
Proof.
  intros.
  pose proof (swapLVarDisjoint (combine swl swr)) as XX.
  specialize (XX lv).
  autorewrite with fast in XX; try congruence.
  apply XX; auto.
Qed.

Lemma swapLVar_subset :
  forall l1 l2 l,
    length l1 = length l2
    -> disjoint l1 l2
    -> disjoint l2 l
    -> no_repeats l2
    -> subset (@swapLVar G vc (combine l1 l2) l)
              (subtractv l l1 ++ l2).
Proof.
  introv len disj1 disj2 norep.
  induction l; simpl; auto.
  apply subset_cons_l.
  allrw disjoint_cons_r; repnd.
  rewrite subtractv_cons; DDeqs; dands; tcsp.

  - pose proof (swapVarIn (combine l1 l2) a) as h.
     autorewrite with fast in h; try congruence;[].
     repeat (autodimp h hyp).
    apply in_app_iff; sp.

  - rw swapVarNoChange; auto;
    autorewrite with fast; try congruence.
Qed.

End SwapProps.

(* one should be able to replace
  [bindersDeep] with [AllVars] thoughout in
  this statement/proof *)
Lemma swapCommonBinders : 
forall {G : CFGV} {vc : VarSym G},
(forall (s : GSym G) (ta : Term s) (sw: Swapping vc)
(lvA : list (vType vc)),
    subset (lvKeep lvA (tBndngVarsDeep vc ta)) (ALDom sw)
    -> disjoint (ALRange sw) (lvA++ (tAllVars ta))
    -> no_repeats (ALRange sw)
    -> disjoint (ALDom sw) (ALRange sw)
    -> disjoint (tBndngVarsDeep vc (tSwap ta sw)) lvA)
    *
(forall (s : GSym G) (pt : Pattern s) (sw: Swapping vc)
(lvA : list (vType vc)),
    subset (lvKeep lvA (pBndngVarsDeep vc pt)) (ALDom sw)
    -> disjoint (ALRange sw) (lvA++ (pAllVars pt))
    -> no_repeats (ALRange sw)
    -> disjoint (ALDom sw) (ALRange sw)
    -> disjoint (pBndngVarsDeep vc (pSwap pt sw)) lvA)
    *
(forall (l : MixtureParam) (ma: Mixture l) (sw: Swapping vc)
(lvA : list (vType vc)),
    subset (lvKeep lvA (mBndngVarsDeep vc ma)) (ALDom sw)
    -> disjoint (ALRange sw) (lvA++ (mAllVars ma))
    -> no_repeats (ALRange sw)
    -> disjoint (ALDom sw) (ALRange sw)
    -> disjoint (mBndngVarsDeep vc (mSwap ma sw)) lvA).
Proof.
  introv. GInduction; cpx; eauto with slow;[| |].
- Case "pvleaf". introv Hsub Hdis Hsdid Hnr.
  allsimpl. rewrite DeqSym. 
  rewrite DeqSym in Hdis.
  rewrite DeqSym in Hsub.
  ddeq; subst; allsimpl; cpx;[].
  repeat(disjoint_reasoning).
  duplicate Hdis.
  eapply swapVarInOrEq in Hdis;cpx.
  dorn Hdis.
  + disjoint_lin_contra.
  + duplicate X. rw Hdis in X.
    rw memberb_din in Hsub.
    revert Hsub. 
    cases_ifd Hs; introv Hsub;cpx.
    unfold subset in Hsub; allsimpl; dLin_hyp; try subst.
    eapply swapVarIn in Hdis1; cpx.
    disjoint_lin_contra.
- Case "mtcons".
  introns Hyp.
  allsimpl. repeat (disjoint_reasoning).
  allrw in_app_iff.
  dorn Hyp5.
  + eapply Hyp in Hyp5; eauto;
    repeat(disjoint_reasoning).
    unfold lvKeep in Hyp1.
    unfold lKeep in Hyp1.
    rw filter_app in Hyp1.
    rw subset_app in Hyp1. repnd.
    cpx.
  + eapply Hyp0 in Hyp5; eauto;
    repeat(disjoint_reasoning).
    unfold lvKeep in Hyp1.
    unfold lKeep in Hyp1.
    rw filter_app in Hyp1.
    rw subset_app in Hyp1. repnd. cpx.
- Case "mpcons".
  introns Hyp.
  allsimpl. repeat (disjoint_reasoning).
  allrw in_app_iff.
  dorn Hyp5.
  + eapply Hyp in Hyp5; eauto;
    repeat(disjoint_reasoning).
    unfold lvKeep in Hyp1.
    unfold lKeep in Hyp1.
    rw filter_app in Hyp1.
    rw subset_app in Hyp1. repnd.
    cpx.
  + eapply Hyp0 in Hyp5; eauto;
    repeat(disjoint_reasoning).
    unfold lvKeep in Hyp1.
    unfold lKeep in Hyp1.
    rw filter_app in Hyp1.
    rw subset_app in Hyp1. repnd. cpx.
Qed.

Lemma tSwapBndngVarsDisjoint : 
forall {G : CFGV} {vc : VarSym G},
(forall (s : GSym G) (ta : Term s) 
(la lb : list (vType vc))
(lvA : list (vType vc)),
    disjoint (tBndngVarsDeep vc ta) lvA
    -> disjoint lb (lvA++ (tAllVars ta))
    -> length la = length lb
    -> no_repeats lb
    -> disjoint la lb
    -> disjoint (tBndngVarsDeep vc (tSwap ta (combine la lb))) lvA).
Proof.
  introv Ha Hb Hc Hd He.
  apply (tcase swapCommonBinders); autorewrite with fast;  cpx.
  unfold lvKeep.
  rewrite lKeepDisjoint; cpx.
  disjoint_reasoning.
Qed.

Lemma SwapEmbedSameBinders : 
  forall {G : CFGV} {vc : VarSym G},
  (forall (s : GSym G) (ta : Term s), True)
  *
  (forall (s : GSym G) (pt : Pattern s) 
  (sw: Swapping vc),
      pBndngVars vc pt 
                = pBndngVars vc (pSwapEmbed pt sw))
  *
  (forall (l : MixtureParam) (ma: Mixture l)
  (sw : Swapping vc),
      mBndngVars vc ma 
                = mBndngVars vc (mSwapEmbed ma sw)).
Proof.
  intros. GInduction; cpx;[].
  Case "mpcons". introns Hyp. intros.
  allsimpl. f_equal; sp.
Qed.

Lemma SwapEmbedSpec : 
  forall {G : CFGV} {vc : VarSym G},
  (forall (s : GSym G) (ta : Term s), True)
  *
  (forall (s : GSym G) (pt : Pattern s) 
  (sw: Swapping vc)
  (lvA : list (vType vc)),
      disjoint lvA (pBndngVars vc pt)
      -> disjoint (lvA++ (pAllButBinders vc pt) 
                        ++ (ALDom sw)) (ALRange sw)
      -> no_repeats (ALRange sw)
      -> disjoint (pAlreadyBndBinders vc pt) lvA
      -> disjoint lvA
                  (pBndngVarsDeep vc
                    (pSwapEmbed pt sw)))
  *
  (forall (l : MixtureParam) (ma: Mixture l)
  (sw : Swapping vc)
  (lvA : list (vType vc)),
  disjoint lvA (mBndngVars vc ma)
  -> disjoint (lvA++ (mAllButBinders vc ma) 
        ++ (ALDom sw)) (ALRange sw)
  -> no_repeats (ALRange sw)
  -> disjoint (mAlreadyBndBinders vc ma) lvA
  -> disjoint lvA (mBndngVarsDeep vc (mSwapEmbed ma sw))
               ).
Proof.
intros. GInduction; cpx;[| |].
- Case "pembed".
  introv ? ? Hpa Hta Hd.
  allsimpl.
  repeat(disjoint_reasoning).
  apply disjoint_sym.
  apply swapCommonBinders; cpx;
  [|repeat(disjoint_reasoning)];[].
  unfold lvKeep.
  rewrite lKeepDisjoint; cpx.
  disjoint_reasoning.
- Case "mtcons".
  introv. intros ? ? Hind ?.
  introv H1a H2a Hd.
  allsimpl.
  repeat (disjoint_reasoning).
  repnud H2a.
  repnud H1a.
  apply Hind; cpx;repeat(disjoint_reasoning).
- Case "mpcons".
  introv. intros  Hpind ? Hmind ?.
  introv H1a H2a Hd H2d.
  allsimpl. repeat(disjoint_reasoning);[|].
  + apply Hpind;
    cpx; dands;repeat(disjoint_reasoning);cpx.
  + apply_hyp;
    cpx; dands;repeat(disjoint_reasoning);cpx.
Qed.

Hint Rewrite
  (fun G vc vsa vs vsb l1 l2 nr1 nr2 => 
    tcase (@swapDisjChain G vc vsa vs vsb l1 l2 nr1 nr2)) : slow.
Hint Rewrite
  (fun G vc vsa vs vsb l1 l2 nr1 nr2 => 
    pcase (@swapDisjChain G vc vsa vs vsb l1 l2 nr1 nr2)) : slow.
Hint Rewrite
  (fun G vc vsa vs vsb l1 l2 nr1 nr2 => 
    mcase (@swapDisjChain G vc vsa vs vsb l1 l2 nr1 nr2)) : slow.

Hint Rewrite (fun G s => @swapVarDisjChain G s) : slow.

Lemma swapLVarApp:
  forall {G : CFGV} {vc : VarSym G}
     (sub : list (vType vc))
    (sa sb : Swapping vc),
       swapLVar sb (swapLVar sa sub)
       = swapLVar (sa ++ sb) sub.
Proof.
  intros. induction sub; cpx;[].
  allsimpl. f_equal; sp; auto.
  simpl.
  autorewrite with SwapAppR.
  refl.
Qed.

Hint Rewrite (fun G vc =>  (@swapLVarApp G vc)) : SwapAppR.
Hint Rewrite <- (fun G vc =>  (@swapLVarApp G vc)) : SwapAppL.


Lemma swapLVarRevCancel :
  forall {G : CFGV} {vc : VarSym G}
    (sub : list (vType vc)) (sw : Swapping vc),
       swapLVar (sw ++ (rev sw)) sub= sub.
Proof.
  intros. induction sub; cpx;[].
  allsimpl. f_equal; sp; auto.
  simpl.
  autorewrite with fast;refl.
Qed.

Hint Rewrite (fun G s => @swapLVarRevCancel G s) : fast.

Lemma swapLVarSwitch :
    forall {G : CFGV} {vc : VarSym G} 
    (sub: list (vType vc))(sw : Swapping vc),
       swapLVar sw sub = swapLVar (ALSwitch sw) sub.
Proof.
  induction sub; cpx.
  intros. simpl.
  f_equal; cpx.
  apply swapVarSwitch.
Qed.

Lemma swapLVarRevNoRep :
  forall {G : CFGV} {vc : VarSym G}
    (sw : Swapping vc) (sub: list (vType vc)),
    no_repeats (ALDom sw)
    -> no_repeats (ALRange sw) 
    -> disjoint (ALDom sw) (ALRange sw)        
    -> swapLVar sw sub = swapLVar (rev sw) sub.
Proof.
  induction sub; cpx.
  intros.
  simpl. f_equal;cpx.
  apply swapVarRevNoRep; auto.
Qed.

Lemma swapLVarDisjChain : forall
  {G : CFGV} {vc : VarSym G}
  (lv : list (vType vc))
  (vsa vs vsb : list (vType vc)),
    length vs = length vsa
    -> length vs = length vsb
    -> no_repeats vs
    -> no_repeats vsb
    -> disjoint vs (vsa ++ vsb ++ lv)
    -> disjoint vsb (vsa ++ lv)
    -> swapLVar ((combine vsa  vs) ++  (combine vs  vsb)) lv
       = swapLVar (combine vsa  vsb) lv.
Proof.
  induction lv; cpx.
  intros.
  allsimpl.
  repeat (disjoint_reasoning).
  f_equal; cpx.
  - apply swapVarDisjChain; cpx; repeat(disjoint_reasoning); cpx.
  - apply IHlv; repeat(disjoint_reasoning); cpx.
Qed.

Hint Rewrite (fun G s => @swapLVarDisjChain G s) : slow.


(** Similar technique should
    work for reversing all
    the proofs about equivariant relations *)
Lemma DisjointEquivariantRev : forall {G : CFGV} {vc : VarSym G}
  la lb (sw : Swapping vc),
  disjoint (swapLVar sw la) (swapLVar sw lb)
  -> disjoint la lb.
Proof.
  introv Hd.
  apply DisjointEquivariant in Hd.
  specialize (Hd (rev sw)).
  rewrite swapLVarApp in Hd.
  rewrite swapLVarApp in Hd.
  autorewrite with fast in Hd.
  trivial.
Qed.

Definition leavesVarUnchanged {G : CFGV} {vc : VarSym G}
  (sw : Swapping vc) (v: vType vc) :=
  (swapVar sw v)= v.
  
Definition leavesLVarUnchanged {G : CFGV} {vc : VarSym G}
  (sw : Swapping vc) (lv: list (vType vc)) :=
  lforall (leavesVarUnchanged sw) lv.  
(** there could be many other ways in which this
    a swapping could leave a var unchanged.
    e.g. cancelling effect.
    see the proof of [alphaEqSwapNonFree]
    from which this concept was inspired
 *)
Lemma leavesLVarUnchanged1 :
  forall {G : CFGV} {vc : VarSym G}
  (sw : Swapping vc) (lv: list (vType vc)),
  disjoint lv (ALDom sw ++ ALRange sw)
  -> leavesLVarUnchanged sw lv.
Proof.
  introv Hdis Hin.
  repeat (disjoint_reasoning).
  unfolds_base. apply swapVarNoChange; cpx.
Qed.

Lemma swapLVarNoChange :
  forall {G : CFGV} {vc : VarSym G}
  (sw : Swapping vc) (lv: list (vType vc)),
  disjoint lv (ALDom sw ++ ALRange sw)
  -> swapLVar sw lv = lv.
Proof.
  induction lv; cpx.
  introns Hyp.
  allsimpl. repeat (disjoint_reasoning).
  f_equal;cpx.
  - apply swapVarNoChange; cpx.
  - apply IHlv. repeat (disjoint_reasoning).
Qed.

Lemma swapVarNonChangeRev:
  forall {G : CFGV} {vc : VarSym G}
  (sw : Swapping vc) (v: (vType vc)),
  swapVar sw v = v
  -> swapVar (rev sw) v = v.
Proof.
  introv Hin.
  rewrite <- Hin at 1.
  autorewrite with SwapAppR.
  autorewrite with fast.
  refl.
Qed.

Lemma swapEmbed_prop_s1_aux :
  forall {G : CFGV} {vc : VarSym G},
    (forall (gs : GSym G) (t : Term gs) (s : Swapping vc),
       True)
    *
    (forall (gs : GSym G) (p : Pattern gs) (s : Swapping vc),
       isReflSwapping s -> pSwapEmbed p s = p)
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs) (s : Swapping vc),
       isReflSwapping s -> mSwapEmbed m s = m).
Proof.
  introv.
  apply GInduction; auto; introv; intros; allsimpl;
  try (f_equal;cpx);
  try (f_equal; apply swap_prop_s1_aux; auto; fail).
Qed.


Hint Rewrite 
  (fun G vc gs t
    => (pcase (@swapEmbed_prop_s1_aux G  vc) gs t [] eq_refl)): fast.

Hint Rewrite 
  (fun G vc gs t
    => (mcase (@swapEmbed_prop_s1_aux G  vc) gs t [] eq_refl)): fast.


Lemma disjointSwapLVar:
  forall  {G : CFGV} {vc : VarSym G} (lva lvb: list (vType vc)) sw, 
  disjoint (lva ++ ALRange sw ++ ALDom sw) lvb
  -> disjoint (swapLVar sw lva) lvb.
Proof.
  induction lva; cpx.
  introv Hdis.
  allsimpl.
  match goal with
  [ |- ?C] => remember C as concl
  end.
  repeat(disjoint_reasoning).
  subst concl.
  apply disjoint_cons_l.
  dands; cpx.
  - apply IHlva; repeat(disjoint_reasoning).
  - pose proof (swapVarImplies sw a ) as XX.
    specialize (XX _ eq_refl).
    repeat(in_reasoning); cpx.
    rw XX; cpx.
Qed.

(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)
