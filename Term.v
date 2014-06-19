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
(** printing #  $\times$ #×# *)
(** printing &  $\times$ #×# *)

Set Implicit Arguments.
(* It is possible to make the typing more precise at the cost
    of complicating some definitions. Term is only meaningful
    for symbols that are not a [PNonTerminal]. Similarly, Pattern is only
    meaningful for symbols that are not [TNonTerminal].
    We (will) prove below that the meaningless types are indeed empty.
*)
(* [vleaf] is a shortcut way to apply the 4th
 kind of production rule *)
(** CatchFileBetweenTagsTermStart*)
Section Gram. Context  {G : CFGV}.
Inductive Term: (GSym G) -> Type :=
| tleaf : forall (T : Terminal G), 
    (tSemType G T) -> Term (gsymT  T)
| vleaf : forall (vc : VarSym G), 
    (vType vc) -> Term (gsymTN (vSubstType G vc))
| tnode : forall (p: TermProd G),
    Mixture (tpRhsAugIsPat p) -> (Term (gsymTN (tpLhs G p)))

with Pattern : (GSym G) -> Type :=
| ptleaf : forall (T : Terminal G), 
    (tSemType G T) -> Pattern (gsymT  T)
| pvleaf : forall (vc : VarSym G), 
    (vType vc) -> Pattern (gsymV vc)
| embed : forall (p: EmbedProd G),
    Term (gsymTN (epRhs G p)) 
       -> Pattern (gsymPN (epLhs G p))
| pnode : forall (p: PatProd G),
    Mixture (map (fun x => (true,x)) (ppRhsSym p))
       -> (Pattern  (gsymPN (ppLhs G p)))

with Mixture : (list (bool * (GSym G))) -> Type :=
| mnil :  Mixture []
| mtcons : forall {h: (GSym G)} {tl: list (bool * (GSym G))},
    Term h -> Mixture tl -> Mixture (((false,h))::tl)
| mpcons : forall {h: (GSym G)} {tl: list (bool * (GSym G))},
    Pattern h ->  Mixture tl -> Mixture ((true,h)::tl).
(** CatchFileBetweenTagsTermEnd*)

(* Question : How can our language model the kind of patterns
    where 2 cases(with same free vars) have the same body. *)




Scheme term_mut := Induction for Term Sort Type
with pat_mut := Induction for Pattern Sort Type
with mix_mut := Induction for Mixture Sort Type.

(** a trivial proof, just to get more
    meaningful variable name *)
Definition GInduction :
forall 
(PT : forall g : GSym G, Term g -> [univ])
(PP : forall g : GSym G, Pattern g -> [univ])
(PM : forall l : MixtureParam, Mixture l -> [univ]),
  (forall (T : Terminal G) (t : tSemType G T), PT (gsymT T) (tleaf T t)) 
  -> (forall (vc : VarSym G) (v : vType vc),
          PT (gsymTN (vSubstType G vc)) (vleaf vc v)) 
  -> (forall (p : TermProd G) (m : Mixture (tpRhsAugIsPat p)),
          PM (tpRhsAugIsPat p) m 
          -> PT (gsymTN (tpLhs G p)) (tnode p m)) 
  -> (forall (T : Terminal G) (t : tSemType G T), PP (gsymT T) (ptleaf T t)) 
  -> (forall (vc : VarSym G) (v : vType vc), 
          PP (gsymV vc) (pvleaf vc v)) 
  -> (forall (p : EmbedProd G) (t : Term (gsymTN (epRhs G p))),
          PT (gsymTN (epRhs G p)) t 
          -> PP (gsymPN (epLhs G p)) (embed p t)) 
  -> (forall (p : PatProd G) 
          (m : Mixture (map (fun x : GSym G => (true, x)) (ppRhsSym p))),
          PM (map (fun x : GSym G => (true, x)) (ppRhsSym p)) m 
          -> PP (gsymPN (ppLhs G p)) (pnode p m)) 
  ->  PM [] mnil 
  ->  (forall (h : GSym G) (tl : MixtureParam) (ph : Term h),
          PT h ph 
          -> forall ptl : Mixture tl,
             PM tl ptl 
             -> PM ((false, h) :: tl) (mtcons ph ptl)) 
  ->  (forall (h : GSym G) (tl : MixtureParam) (ph : Pattern h),
          PP h ph 
          -> forall ptl : Mixture tl,
              PM tl ptl 
              -> PM ((true, h) :: tl) (mpcons ph ptl)) 
  -> ((forall (g : GSym G) (p : Term g), PT g p)
         *
      (forall (g : GSym G) (p : Pattern g), PP g p)
         *
      (forall (l : list (bool # GSym G)) (m : Mixture l), PM l m)).
Proof.
  intros. split; [split|];[ | | ].
  - eapply term_mut; eauto.
  - eapply pat_mut; eauto.
  - eapply mix_mut; eauto.
Defined.

Definition TermInd :=
  (fun PT PP PM a b c d e f g h i j =>
    fst (fst (@GInduction PT PP PM a b c d e f g h i j))).

Definition PatInd :=
  (fun PT PP PM a b c d e f g h i j =>
    snd (fst (@GInduction PT PP PM a b c d e f g h i j))).

Fixpoint PatInMix  {s :GSym G} 
{l : list (bool # GSym G)}
(pt : Pattern s)
(mix : Mixture l) : [univ] :=
match mix with
| mnil => False
| mpcons s' _ h mtl => {p : s =s' $ transport p pt = h} [+] (PatInMix pt mtl)
| mtcons s' _ h mtl =>  (PatInMix pt mtl)
end.

(* A more specialized lemma for induction on Patterns
    Thy benefits are
    - It exploits the fact that
       the mixtures at pattern nodes do not have terms.
    - the proposition on Patterns is lifted to one on
      Mixture of patterns automatically using the default
      pointwise semantics. So the user need not supply
      a predicate on Mixture, i.e. there is no PM
  For simplicity, it also assumes that there are no embeddings.
  In case of embeddings, these simplications dont seem to be possible
*)

Lemma PatIndNoEmbed :
forall 
(PP : forall g : GSym G, Pattern g -> [univ]),
  (EmbedProd G-> False)
  -> (forall (T : Terminal G) (t : tSemType G T), PP (gsymT T) (ptleaf T t)) 
  -> (forall (vc : VarSym G) (v : vType vc), 
          PP (gsymV vc) (pvleaf vc v)) 
  -> (forall (p : PatProd G)
          (m : Mixture (map (fun x : GSym G => (true, x)) (ppRhsSym p))),
          (forall (s : GSym G) (pt : Pattern s),
              PatInMix pt m
              -> PP s pt)
          -> PP (gsymPN (ppLhs G p)) (pnode p m))
  -> (forall (g : GSym G) (p : Pattern g), PP g p).
Proof.
  introv Hnod Ht Hv Hem.
  induction p using pat_mut
  with (P:=(fun x y=> True))
        (P1:= (fun l m=> (forall (s : GSym G) (pt : Pattern s),
                              PatInMix pt m
                              -> PP s pt))); auto; try contradiction.
  - introv Hin.
    simpl in Hin. dorn Hin.
    + exrepnd.
      unfold transport in Hin0.
      generalize dependent pt. rw p0.
      simpl. intros. auto. rw Hin0.
      auto.
    + apply IHp0. auto.
Qed.


Fixpoint TermInMix {s :GSym G}
{l : list (bool # GSym G)}
(tt : Term s)
(mix : Mixture l) : [univ] :=
match mix with
| mnil => False
| mtcons s' _ h mtl => {p : s =s' $ transport p tt = h} [+] (TermInMix tt mtl)
| mpcons s' _ h mtl =>  (TermInMix tt mtl)
end.
  

Definition MixInd :=
  (fun PT PP PM a b c d e f g h i j =>
    snd (@GInduction PT PP PM a b c d e f g h i j)).

Lemma TermIndNoPat :
forall  
(PT : forall g : GSym G, Term g -> [univ]),
  (forall (T : Terminal G) (t : tSemType G T), PT (gsymT T) (tleaf T t)) 
  -> (forall (vc : VarSym G) (v : vType vc),
          PT (gsymTN (vSubstType G vc)) (vleaf vc v)) 
  -> (forall (p : TermProd G) (m : Mixture (tpRhsAugIsPat p)),
          (forall (s : GSym G) (pt : Term s),
              TermInMix pt m
              -> PT s pt)
          -> PT (gsymTN (tpLhs G p)) (tnode p m)) 
  -> (forall (g : GSym G) (p : Term g), PT g p).
Proof.
  introv Ht Hv Hem.
  induction p using term_mut
  with (P0:=(fun x y=> True))
        (P1:= (fun l m=> (forall (s : GSym G) (tt : Term s),
                              TermInMix tt m
                              -> PT s tt))); auto; try contradiction.
  - introv Hin.
    simpl in Hin. dorn Hin.
    + exrepnd.
      unfold transport in Hin0.
      generalize dependent tt. rw p0.
      simpl. intros. auto. rw Hin0.
      auto.
    + apply IHp0. auto.
Qed.
End Gram.

Ltac GInductionAux lemma :=
  apply lemma ; [
                        Case "tleaf"
                      | Case "vleaf"
                      | Case "tnode"
                      | Case "ptleaf"
                      | Case "pvleaf"
                      | Case "pembed"
                      | Case "pnode"
                      | Case "mnil"
                      | Case "mtcons"
                      | Case "mpcons"
].

Tactic Notation "GInduction" :=
  GInductionAux GInduction.

(** CatchFileBetweenTagsBndngVarsStart *)
Fixpoint pBndngVars {G} (vc : VarSym G)
   {gs}  (p : Pattern gs) : (list (vType vc)) :=
match p with
| ptleaf _ _ => []  | embed _ _ => []
| pvleaf vcc var => match (DeqVarSym vcc vc) with
                   | left eqq => [transport eqq var]
                   | right _ => []
                   end
| pnode _ mix => mBndngVars vc mix
end
with mBndngVars {G} (vc: VarSym G) {lgs}
  (pts : Mixture lgs) : (list (vType vc)) := 
match pts with
| mnil => []  | mtcons _ _ _ tl =>  mBndngVars vc tl
| mpcons _ _ h tl => (pBndngVars vc h) ++ mBndngVars vc tl
end.
(** CatchFileBetweenTagsBndngVarsEnd *)


(** CatchFileBetweenTagsBVarsNthStart *)
Fixpoint getBVarsNth {G} (vc  : VarSym G) {lgs}
  (pts : Mixture lgs) (n : nat) : (list (vType vc)) :=
match (pts,n) with
| (mnil,_) => []  | (mtcons _ _ ph pth, 0)  => [] 
| (mpcons _ _ ph pth, 0) => (pBndngVars vc ph)
| (mtcons _ _ ph pth, S m) => (getBVarsNth vc pth m)
| (mpcons _ _ ph pth, S m) => (getBVarsNth vc pth m)
end.
(** CatchFileBetweenTagsBVarsNthEnd *)


Definition removev {G : CFGV} {vc : VarSym G} v l :=
  remove (DeqVtype vc) v l.

Definition subtractv
           {G : CFGV}
           { vc  : VarSym G}
           (vlhs : list (vType vc))
           (vrhs : list (vType vc)) :  list (vType vc) :=
  diff (DeqVtype vc) vrhs vlhs.

(* begin hide *)
Fixpoint lBoundVarsOld {G : CFGV} { vc  : VarSym G}
  {ls : list (bool * (GSym G))}
  (llbn : list (list nat)) (lmix : Mixture ls)
  : list( (list (vType vc))) :=
match llbn with
| [] => []
| (lnh::lntl)
    => (flat_map (getBVarsNth vc lmix) lnh)
       :: (lBoundVarsOld lntl lmix)
end.
(* end hide *)

(* given an element in rhs, finds the set of binders that are bound to it.
    These vars have to be removed while computing freevars *)
Definition lBoundVars {G : CFGV} ( vc  : VarSym G)
  {ls : list (bool * (GSym G))}
  (llbn : list (list nat)) (lmix : Mixture ls)
  : list( (list (vType vc))) :=
map (flat_map (getBVarsNth vc lmix)) llbn.

Definition  allBndngVars {G} (vc: VarSym G) (p: TermProd G) 
  (mix: Mixture (tpRhsAugIsPat p)) : list(list (vType vc)) :=
   lBoundVars vc (bndngPatIndices p) mix.

Module SimplifyForPaper.
(** CatchFileBetweenTagsAllBndngVarsStart *)

Definition allBndngVars {G} (vc : VarSym G) 
    (p: TermProd G) (mix: Mixture (tpRhsAugIsPat p)) 
    : list ( list (vType vc)) :=
map (flat_map (getBVarsNth vc mix)) (bndngPatIndices p).
(** CatchFileBetweenTagsAllBndngVarsEnd *)
End SimplifyForPaper.

Lemma  lBoundVarsSameifNth :  forall {G : CFGV} 
  ( vc  : VarSym G)
{la : list (bool # GSym G)} (ma mb: Mixture la),
  (forall (nn : nat),
    getBVarsNth vc ma nn = getBVarsNth vc mb nn)
  -> forall (lln : list (list nat)),
  lBoundVars vc lln ma =  lBoundVars vc lln mb.
Proof.
  intros. unfold lBoundVars.
  apply eq_maps.
  intros n Hin.
  apply eq_flat_maps.
  intros nn Hinn. cpx.
Qed.

Lemma  lBoundVarsLenSameifNth :  forall {G : CFGV} 
  ( vc  : VarSym G)
{la : list (bool # GSym G)} (ma mb: Mixture la),
  (forall (nn : nat),
  length (getBVarsNth vc ma nn) = 
        length (getBVarsNth vc mb nn))
  -> forall (lln : list (list nat)),
  map (@length _) (lBoundVars vc lln ma) 
  =  map (@length _) (lBoundVars vc lln mb).
Proof.
  intros. unfold lBoundVars.
  rewrite map_map.
  rewrite map_map.
  unfold compose.
  apply eq_maps.
  intros n Hin.
  clear Hin.
  induction n; allsimpl; cpx.
  rewrite length_app.
  rewrite length_app.
  f_equal; cpx.
Qed.

Lemma sdkfd: forall {G : CFGV} { vc  : VarSym G}
  {ls : list (bool * (GSym G))}
(llbn : list (list nat)) (lmix : Mixture ls)
  ,
lBoundVarsOld llbn lmix  = lBoundVars vc llbn lmix .
Proof.
  induction llbn; intros; allsimpl; cpx.
  f_equal.
  auto.
Qed.

(*
Fixpoint onNth {T : Type} {G : CFGV}
  {lgs : MixtureParam}
  (ft: forall (gs : (GSym G)) (p : Term gs), T)
  (fp: forall (gs : (GSym G)) (p : Pattern gs), T)
  (nilCase : T)
  (pts : Mixture lgs) 
  (n : nat) : T :=
match (pts,n) with
| (mnil,_) => nilCase
| (mtcons sh _ th pth, 0)  => ft sh th
| (mpcons sh _ ph pth, 0) => fp sh ph
| (mtcons _ _ ph pth, S m)
| (mpcons _ _ ph pth, S m) => (onNth ft fp nilCase pth m)
end.
*)

Fixpoint MixMap
{T : Type} {G : CFGV}
  {lgs : MixtureParam}
  (ft: forall (gs : (GSym G)) (p : Term gs), T)
  (fp: forall (gs : (GSym G)) (p : Pattern gs), T)
  (pts : Mixture lgs) 
   : list T :=
match pts with
| mnil => []
| mtcons sh _ th ttl  => (ft sh th)::(MixMap ft fp ttl)
| mpcons sh _ ph ptl => (fp sh ph)::(MixMap ft fp ptl)
end.

Lemma MixMapLength : forall
{T : Type} {G : CFGV}
  {lgs : MixtureParam}
  (ft: forall (gs : (GSym G)) (p : Term gs), T)
  (fp: forall (gs : (GSym G)) (p : Pattern gs), T)
  (pts : Mixture lgs),
    length (MixMap ft fp pts) = length lgs.
Proof.
  induction pts; cpx.
Qed.

Fixpoint liftRelPtwise
{T : Type} {G : CFGV}
  {lgs : MixtureParam}
  (ft: forall (gs : (GSym G)) (p : Term gs), T -> [univ])
  (fp: forall (gs : (GSym G)) (p : Pattern gs), T -> [univ])
  (pts : Mixture lgs) 
  (l : list T)
   : [univ]:=
match (pts,l) with
| (mnil,[]) => True
| (mtcons sh _ th ttl, lh::ltl) => (ft sh th lh)#(liftRelPtwise ft fp ttl ltl)
| (mpcons sh _ th ttl, lh::ltl) => (fp sh th lh)#(liftRelPtwise ft fp ttl ltl)
| _ => False
end.

Hint Rewrite (fun T => @MixMapLength T): fast.

Fixpoint tAllVars {G : CFGV} { vc  : VarSym G}
  {gs : (GSym G)} (t : Term gs)
   {struct t} : (list (vType vc))  :=
match t with
| tleaf _ _ => []
| vleaf vcc var => match (DeqVarSym vcc vc) with
                   | left eqq => [transport eqq var]
                   | right _ => []
                   end
| tnode _ mix => mAllVars mix
end
with pAllVars {G : CFGV} { vc  : VarSym G}
  {gs : (GSym G)} (p : Pattern gs)
   {struct p} : (list (vType vc))  :=
match p with
| ptleaf _ _ => []
| pvleaf vcc var => match (DeqVarSym vcc vc) with
                   | left eqq => [transport eqq var]
                   | right _ => []
                   end
| pnode _ mix => mAllVars mix
| embed _ t => tAllVars t
end
with mAllVars {G : CFGV} { vc  : VarSym G}
  {lgs : list (bool * GSym G)} (pts : Mixture lgs)
   {struct pts} : (list (vType vc))  := 
match pts with
| mnil => []
| mtcons _ _ ph ptl =>  (tAllVars ph) ++ (mAllVars ptl)
| mpcons _ _ ph ptl => (pAllVars ph) ++ (mAllVars ptl)
end.

Lemma mBndngVarsAsNth  {G : CFGV} { vc  : VarSym G} :
  forall 
  (mp: @MixtureParam G) 
  (m : Mixture mp),
  mBndngVars vc m 
      = flat_map (getBVarsNth vc  m) (seq 0 (length mp)).
Proof.
  intros.
  induction m; cpx; allsimpl.
  - simpl. rw IHm. rw <- seq_shift.
    rw  flat_map_map. unfold compose.
    auto.
  - rw IHm. rw <- seq_shift.
    rw  flat_map_map. unfold compose.
    auto.
Qed.

Fixpoint tSize {G : CFGV}
  {gs : (GSym G)} (t : Term gs)
   {struct t} : nat :=
match t with
| tleaf _ _ => 1
| vleaf vcc var => 1
| tnode _ mix => mSize mix
end
with pSize {G : CFGV}
  {gs : (GSym G)} (p : Pattern gs)
   {struct p} : nat  :=
match p with
| ptleaf _ _ => 1
| pvleaf vcc var => 1
| pnode _ mix => mSize mix
| embed _ t => 1 + tSize t
end
with mSize {G : CFGV}
  {lgs : list (bool * GSym G)} (pts : Mixture lgs)
   : nat  := 
match pts with
| mnil => 1
| mtcons _ _ ph ptl =>  (tSize ph) + (mSize ptl)
| mpcons _ _ ph ptl => (pSize ph) + (mSize ptl)
end.

Lemma SizePositive :forall  {G : CFGV},
     (  (forall (s : GSym G) (t : Term s),
            tSize t > 0 )
         *
        (forall (s : GSym G) (pt : Pattern s),
            pSize pt > 0)
         *
        (forall (l : @MixtureParam G) (m : Mixture l),
            mSize m > 0)).
Proof.
  intros. 
  GInduction; intros; allsimpl; try omega.
Qed.

Definition mcase := snd.
Definition tcase {A B C : Type}
  := fun t:A*B*C => fst (fst t).
Definition pcase {A B C : Type}
  := fun t:A*B*C => snd (fst t).

Lemma GInductionS :
forall {G: CFGV}
(PT : forall g : GSym G, Term g -> [univ])
(PP : forall g : GSym G, Pattern g -> [univ])
(PM : forall l : MixtureParam, Mixture l -> [univ]),
  (forall (T : Terminal G) (t : tSemType G T), PT (gsymT T) (tleaf T t)) 
  -> (forall (vc : VarSym G) (v : vType vc),
          PT (gsymTN (vSubstType G vc)) (vleaf vc v)) 
  -> (forall (p : TermProd G) (m : Mixture (tpRhsAugIsPat p)),
          PM (tpRhsAugIsPat p) m 
          -> PT (gsymTN (tpLhs G p)) (tnode p m)) 
  -> (forall (T : Terminal G) (t : tSemType G T), PP (gsymT T) (ptleaf T t)) 
  -> (forall (vc : VarSym G) (v : vType vc), 
          PP (gsymV vc) (pvleaf vc v)) 
  -> (forall (p : EmbedProd G) (t : Term (gsymTN (epRhs G p))),
          PT (gsymTN (epRhs G p)) t 
          -> PP (gsymPN (epLhs G p)) (embed p t)) 
  -> (forall (p : PatProd G) 
          (m : Mixture (map (fun x : GSym G => (true, x)) (ppRhsSym p))),
          PM (map (fun x : GSym G => (true, x)) (ppRhsSym p)) m 
          -> PP (gsymPN (ppLhs G p)) (pnode p m)) 
  ->  PM [] mnil 
  ->  (forall (h : GSym G) (tl : MixtureParam) (ph : Term h),
         (forall (phnew:Term h), tSize phnew <= tSize ph -> PT h phnew)
          -> forall ptl : Mixture tl,
             PM tl ptl
             -> PM ((false, h) :: tl) (mtcons ph ptl)) 
  ->  (forall (h : GSym G) (tl : MixtureParam) (ph : Pattern h),
         (forall (phnew:Pattern h), pSize phnew <= pSize ph -> PP h phnew)
          -> forall ptl : Mixture tl,
              PM tl ptl 
              -> PM ((true, h) :: tl) (mpcons ph ptl)) 
  -> ((forall (g : GSym G) (p : Term g), PT g p)
         *
      (forall (g : GSym G) (p : Pattern g), PP g p)
         *
      (forall (l : list (bool # GSym G)) (m : Mixture l), PM l m)).
Proof.
  introns Hyps.
assert( forall n: nat,
(
  (forall (g : GSym G) (p : Term g), (tSize p = n) -> PT g p)
  * (forall (g : GSym G) (p : Pattern g), (pSize p = n) -> PP g p)
  * (forall (l : list (bool # GSym G)) (m : Mixture l), 
      (mSize m = n) -> PM l m)
)) as XX;
    [|
    dands; intros; 
     try(apply ((tcase (XX _)) _ _ eq_refl));
     try(apply ((pcase (XX _)) _ _ eq_refl));
     try(apply ((mcase (XX _)) _ _ eq_refl)); fail].
  induction n as [n Hind] using comp_ind_type.
  GInduction; introns HGInd; allsimpl; cpx.
  - Case "pembed". apply Hyps4. specialize (Hind (tSize t)).
    dimp Hind; try omega;[]. repnd.
    cpx.
  - Case "mtcons". apply Hyps7.
    + introv Hlt.
      pose proof (mcase SizePositive _  ptl).
      specialize (Hind (tSize phnew)).
      dimp Hind; try omega;[]. repnd. cpx.
    + pose proof (tcase SizePositive _  ph).
      specialize (Hind (mSize ptl)).
      dimp Hind; try omega;[]. repnd. cpx.
  - Case "mpcons". apply Hyps8.
    + introv Hlt.
      pose proof (mcase SizePositive _  ptl).
      specialize (Hind (pSize phnew)).
      dimp Hind; try omega;[]. repnd. cpx.
    + pose proof (pcase SizePositive _  ph).
      specialize (Hind (mSize ptl)).
      dimp Hind; try omega;[]. repnd. cpx.
Defined.


Tactic Notation "GInductionS" :=
  GInductionAux GInductionS.

Lemma lBoundVarsLength : forall G
  {mp : MixtureParam} (vc : VarSym G)
  (m : Mixture mp) lln,
length (lBoundVars vc lln m) = length lln.
Proof.
  intros. unfold lBoundVars.
  autorewrite with fast. refl.
Qed.

Hint Rewrite lBoundVarsLength : fast.



Definition lvKeep {G : CFGV} 
  {vc  : VarSym G}
  (lvKeep : list (vType vc))
  (lv : list (vType vc)) := 
lKeep (DeqVtype vc) lvKeep lv.



(* gets all but binders.
  The intention is that for any vc,
  [mAllButBinders m = mAllvars m -  mBndngVars m] 
 *)
Fixpoint pAllButBinders
       {G  : CFGV}
       {gs : GSym G}
       (vc : VarSym G)
       (pt : Pattern gs)
        {struct pt} : (list (vType vc))  :=
  match pt with
    | ptleaf a v => []
    | pvleaf vcc var => []
    | pnode p lpt => mAllButBinders vc lpt
    | embed p nt => tAllVars nt
  end
with mAllButBinders
       {G  : CFGV}
       {lgs : list (bool * GSym G)}
       (vc : VarSym G)
       (pts : Mixture lgs)
       {struct pts}
     : (list (vType vc))  :=
  match pts with
    | mnil  => []
    | mtcons _ _ ph ptl => 
            (tAllVars ph) ++ (mAllButBinders vc ptl)
    | mpcons _ _ ph ptl =>
           (pAllButBinders vc ph) ++ (mAllButBinders vc ptl)
  end.

Fixpoint tBndngVarsDeep {G : CFGV} (vc : VarSym G)
  {gs : (GSym G)} (t : Term gs)
   {struct t} : (list (vType vc))  :=
match t with
| tleaf _ _ => []
| vleaf vcc var => []
| tnode _ mix => mBndngVarsDeep vc mix
end
with pBndngVarsDeep {G : CFGV} (vc : VarSym G)
  {gs : (GSym G)} (p : Pattern gs)
   {struct p} : (list (vType vc))  :=
match p with
| ptleaf _ _ => []
| pvleaf vcc var => match (DeqVarSym vcc vc) with
                   | left eqq => [transport eqq var]
                   | right _ => []
                   end
| pnode _ mix => mBndngVarsDeep vc mix
| embed _ t => tBndngVarsDeep vc t
end
with mBndngVarsDeep {G : CFGV} (vc : VarSym G)
  {lgs : list (bool * GSym G)} (pts : Mixture lgs)
   {struct pts} : (list (vType vc))  := 
match pts with
| mnil => []
| mtcons _ _ ph ptl =>  (tBndngVarsDeep vc ph) ++ (mBndngVarsDeep vc ptl)
| mpcons _ _ ph ptl => (pBndngVarsDeep vc ph) ++ (mBndngVarsDeep vc ptl)
end.


(* get already bound binders deeply.
    the yet to be bound binders are
    not yet guaranteed to be disjoint
    fron [lvA] in [mRenAlpha] *)
Fixpoint pAlreadyBndBinders
       {G  : CFGV}
       {gs : GSym G}
       (vc : VarSym G)
       (pt : Pattern gs)
        {struct pt} : (list (vType vc))  :=
  match pt with
    | ptleaf a v => []
    | pvleaf vcc var => []
    | pnode p lpt => mAlreadyBndBinders vc lpt
    | embed p nt => tBndngVarsDeep vc nt
  end
with mAlreadyBndBinders
       {G  : CFGV}
       {lgs : list (bool * GSym G)}
       (vc : VarSym G)
       (pts : Mixture lgs)
       {struct pts}
     : (list (vType vc))  :=
  match pts with
    | mnil  => []
    | mtcons _ _ ph ptl => 
            (tBndngVarsDeep vc ph) ++ (mAlreadyBndBinders vc ptl)
    | mpcons _ _ ph ptl =>
           (pAlreadyBndBinders vc ph) ++ (mAlreadyBndBinders vc ptl)
  end.

(* patterns do not have internal bindings 
    (members of [PatProd] do not specify binding info).
   Hence the [nil] *)

Infix "--" 
  := subtractv (right associativity, at level 60) : list_scope.

(** CatchFileBetweenTagsFreevarsStart *)

Fixpoint tfreevars {G}(vc : VarSym G) {gs} 
    (p : Term gs) : list (vType vc) :=
match p with
| tleaf _ _ => []
| vleaf vcc var =>  match (DeqVarSym vcc vc) with
                   | left eqq => [transport eqq var]
                   | right _ => []
                   end
| tnode p m => mfreevars vc m (allBndngVars vc p m)
end
with pfreevars {G} (vc : VarSym G) {gs} 
    (p : Pattern gs) : list (vType vc)  :=
match p with
| ptleaf _ _ => []  | pvleaf vcc var => []
| pnode p lpt => mfreevars vc lpt [] 
| embed vcc nt => tfreevars vc nt
end
with mfreevars {G} (vc: VarSym G) {lgs} (m: Mixture lgs)
  (llB : list (list (vType vc))) : list (vType vc) := 
match m with
| mnil  => []
| mtcons _ _ h tl => (tfreevars vc h -- lhead llB) 
                        ++ mfreevars vc tl (tail llB)
| mpcons _ _ h tl => (pfreevars vc h -- lhead llB)
                        ++ mfreevars vc tl (tail llB)
end.

(** CatchFileBetweenTagsFreevarsEnd *)

Require Import Eqdep_dec.

Ltac one_ddeq :=
  match goal with
    | [ |- context[DeqVarSym ?x ?y] ] => destruct (DeqVarSym x y)
    | [ H : context[DeqVarSym ?x ?y] |- _ ] => destruct (DeqVarSym x y)
    | [ |- context[DeqVtype ?x ?y ?z] ] => destruct (DeqVtype x y z)
    | [ H : context[DeqVtype ?x ?y ?z] |- _ ] => destruct (DeqVtype x y z)
    | [ |- context[in_deq_t ?t (DeqVtype ?x) ?y ?z] ] => destruct (in_deq_t t (DeqVtype x) y z)
    | [ H : context[in_deq_t ?t (DeqVtype ?x) ?y ?z] |- _ ] => destruct (in_deq_t t (DeqVtype x) y z)
    | [ e : ?v = ?v |- _ ] =>
      let x := fresh "x" in
      assert (e = eq_refl) as x by (apply UIP_dec; apply DeqVarSym);
        subst e
  end.

Ltac ddeq := repeat one_ddeq.

Ltac on_eq :=
  match goal with
    | [ H : ?x = ?y |- _ ] => first [ subst x | subst y ]
    | [ H : ?x <> ?x |- _ ] => provefalse; apply H; complete auto
  end.
Ltac on_eqs := repeat on_eq.

Ltac DDeq := repeat (one_ddeq; on_eqs; GC; auto).

Ltac DDeqs := repeat (one_ddeq; on_eqs; GC; allsimpl; auto).

Lemma bindersDeep_in_allvars : forall 
  {G : CFGV} {vc : VarSym G},
  
  (
    (forall (gs : GSym G) (t : Term gs),
       subset (tBndngVarsDeep vc t) (tAllVars t))
    *
    (forall (gs : GSym G) (p : Pattern gs),
       subset (pBndngVarsDeep vc p) (pAllVars p))
    *
    (forall (lgs : list (bool * GSym G)) (m : Mixture lgs),
       subset (mBndngVarsDeep vc m) (mAllVars m))
  ).
Proof.
  intros. GInduction; auto; introv;
  try (complete (allsimpl; cpx));
  try (complete (allsimpl; introv f e; DDeqs; cpx)).

  - Case "mtcons".
    allsimpl.
    introv T M; introv i.
    allrw in_app_iff; sp.

  - Case "mpcons".
    allsimpl.
    introv P M; introv i.
    allrw in_app_iff; sp.
Qed.

Lemma subtractv_app_r : forall {G : CFGV} {vc : VarSym G}
  (l1 l2 l : list (vType vc)),
    subtractv l (l1 ++ l2) = subtractv (subtractv l l2) l1.
Proof.
  unfold subtractv; introv.
  rw diff_app_l; sp.
Qed.

Lemma subtractv_disjoint_subset : 
forall {G : CFGV} {vc : VarSym G}
  (vs l1 l2 : list (vType vc)),
    subset l1 l2
    -> disjoint l1 (subtractv vs l2).
Proof.
  unfold subtractv.
  introv ss i j.
  allrw in_diff; sp.
Qed.

Lemma subtractv_disjoint : 
  forall {G : CFGV} {vc : VarSym G}
  vs l, disjoint l (@subtractv G vc vs l).
Proof.
  unfold subtractv; introv i j.
  allrw in_diff; sp.
Qed.
Hint Immediate subtractv_disjoint.

Lemma subtractv_cons :
  forall {G : CFGV} {vc : VarSym G}
  a l1 l2,
    @subtractv G vc (a :: l1) l2
    = if in_deq_t (vType vc) (DeqVtype vc) a l2
      then subtractv l1 l2
      else a :: (subtractv l1 l2).
Proof.
  unfold subtractv, removev; simpl; introv.
  rw diff_cons_r.
  remember (memberb (DeqVtype vc) a l2); destruct b; symmetry in Heqb;
  [rw fold_assert in Heqb | rw not_of_assert in Heqb];
  rw (@assert_memberb (vType vc)) in Heqb;
  destruct (in_deq_t (vType vc) (DeqVtype vc) a l2); sp.
Qed.


Theorem AllButBindersSubset: forall 
  {G : CFGV} {vc  : VarSym G},
(   forall (s : GSym G) (nt : Term s),
      True)
*
(   forall (s : GSym G) (pt : Pattern s),
    subset (pAllButBinders vc pt )
           (pAllVars  pt)
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l),
    subset (mAllButBinders vc m)
           (mAllVars m)
).
Proof. intros.
  GInduction; intros; cpx; allsimpl; 
  eauto using subset_app_l, subset_app_r;
  apply app_subset;
  dands; eauto using subset_app_l, subset_app_r.
Qed.

Lemma getBVarsNthRange :
forall {G : CFGV} {vc  : VarSym G} (mp : MixtureParam) 
  (m : Mixture mp) (nn: nat), 
    nn >= length mp 
    -> (getBVarsNth vc m nn) = [].
Proof.
  induction m; introv Hgt; cpx;
  [Case "mtcons"|Case "mpcons"]; allsimpl.
  - simpl. allunfold ge.
    destruct nn; cpx.
    apply IHm.
    omega.
  - simpl. allunfold ge.
    destruct nn; cpx; try omega;[].
    apply IHm.
    omega.
Qed.

Lemma getBVarsNthRangeContra :
forall {G : CFGV} {vc  : VarSym G} (mp : MixtureParam) 
  (m : Mixture mp) (nn: nat)
  (x : vType vc),
  LIn x (getBVarsNth vc m nn)
  -> nn < length mp.
Proof.
  introv Hin.
  destruct (le_lt_dec (length mp) nn); cpx.
  rewrite getBVarsNthRange in Hin; cpx.
Qed.

Lemma lBoundVarsmBndngVars :
forall {G : CFGV} {vc  : VarSym G} (mp : MixtureParam) 
  (m : Mixture mp) 
  (lll : list (list nat)),
  subset (flatten (lBoundVars vc lll m))
         (mBndngVars vc m ).
Proof.
  introv Hin.
  rw lin_flat_map in Hin.
  exrepnd. rw in_map_iff in Hin1.
  exrepnd. rewrite mBndngVarsAsNth.
  subst. apply lin_flat_map in Hin0.
  exrepnd. rename x0 into nn.
  apply lin_flat_map.
  exists nn. dands;spc.
  apply getBVarsNthRangeContra in Hin2.
  apply LInSeqIff; dands; omega.
Qed.


Lemma bindersSubsetDeep: forall {G : CFGV} {vc  : VarSym G},
(   forall (s : GSym G) (nt : Term s), True)
*
(   forall (s : GSym G) (pt : Pattern s),
    subset (pBndngVars vc pt )
           (pBndngVarsDeep vc pt)
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l),
    subset (mBndngVars vc m)
           (mBndngVarsDeep vc m)
).
Proof.
  intros. GInduction; intros; cpx; allsimpl; 
  eauto using subset_app_l, subset_app_r;
  [Case "mpcons"].
  apply app_subset.
  dands; eauto using subset_app_l, subset_app_r.
Qed.

Theorem bindersAllvarsSubset: forall {G : CFGV} {vc  : VarSym G},
(   forall (s : GSym G) (nt : Term s),
      True)
*
(   forall (s : GSym G) (pt : Pattern s),
    subset (pBndngVars vc pt )
           (pAllVars  pt)
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l),
    subset (mBndngVars vc m)
           (mAllVars m)
).
Proof.
  intros. GInduction; intros; cpx; allsimpl; 
  eauto using subset_app_l, subset_app_r;
  [Case "mpcons"].
  apply app_subset.
  dands; eauto using subset_app_l, subset_app_r.
Qed.

Hint Resolve 
  (fun G vc => mcase (@ AllButBindersSubset G vc)) 
  (fun G vc => pcase (@ AllButBindersSubset G vc)) 
  (fun G vc => mcase (@ bindersAllvarsSubset G vc)) 
  (fun G vc => pcase (@ bindersAllvarsSubset G vc)) 
  (fun G vc => mcase (@ bindersSubsetDeep G vc)) 
  (fun G vc => pcase (@ bindersDeep_in_allvars G vc)) 
  (fun G vc => mcase (@ bindersDeep_in_allvars G vc)) 
  (fun G vc => tcase (@ bindersDeep_in_allvars G vc)) 
  lBoundVarsmBndngVars
  : SetReasoning.

Lemma  mBndngVarsSameIfNth :  forall {G : CFGV} 
  ( vc  : VarSym G)
{la : list (bool # GSym G)} (ma mb: Mixture la),
  (forall (nn : nat),
    getBVarsNth vc ma nn = getBVarsNth vc mb nn)
  -> mBndngVars vc ma =  mBndngVars vc mb.
Proof.
  intros. rewrite mBndngVarsAsNth.
  rewrite mBndngVarsAsNth.
  apply  eq_flat_maps.
  intros nn Hinn. cpx.
Qed.


Lemma eqSetDeepShallowPlusAlready: 
forall {G : CFGV} {vc  : VarSym G},
(   forall (s : GSym G) (nt : Term s), True)
*
(   forall (s : GSym G) (pt : Pattern s),
    eqset (pBndngVarsDeep vc pt )
          (pBndngVars vc pt ++ pAlreadyBndBinders vc pt)
)
*
(   forall (l : list (bool # GSym G)) (m : Mixture l),
    eqset (mBndngVarsDeep vc m)
          (mBndngVars vc m ++ mAlreadyBndBinders vc m)
).
Proof.
  intros. GInduction;  intros; cpx.
- Case "pvleaf".
  simpl; ddeq; cpx.
- Case "mtcons".
  allsimpl. eapply eqset_trans;[|apply eqsetCommute].
  rw <- app_assoc.
  apply eqset_app_if; cpx.
  eapply eqset_trans;[|apply eqsetCommute]; cpx.

- Case "mpcons".
  allsimpl. 
  eapply eqset_trans;[|apply eqsetCommute3].
  rw <- app_assoc.
  rw  app_assoc.
  apply eqset_app_if; cpx.
  eapply eqset_trans;[|apply eqsetCommute]. cpx.
Qed.

Lemma disjointDeepShallowPlusAlready: 
forall {G : CFGV} {vc  : VarSym G}
  (l : list (bool # GSym G)) (m : Mixture l) lva,
  disjoint (mBndngVars vc m ++ mAlreadyBndBinders vc m) lva
  -> disjoint  (mBndngVarsDeep vc m) lva.
Proof.
  introv Hdis.
  SetReasoning.
  apply eqsetSubset.
  apply eqset_sym.
  apply  eqSetDeepShallowPlusAlready.
Qed.
(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)
