(*
(C) Copyright 2010, COQTAIL team

Project Info: http://sourceforge.net/projects/coqtail/

This library is free software; you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 2.1 of the License, or
(at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
USA.
*)

Require Import Ensembles.
Require Import Powerset.

(** * Infinite Union *)

Inductive Infinite_Union (U:Type) (I:Type) (Ai : I -> Ensemble U) : Ensemble U :=
  Infinite_Union_intro : forall x:U,
    (exists i:I, In _ (Ai i) x) ->
    In _ (Infinite_Union U I Ai) x.

(** * Topological space *)

Class Topological_Space
    (X:Type)
    (set : Ensemble X)
    (topology : Ensemble (Ensemble _))
  := {
  open_empty_set : In (Ensemble X) topology (Empty_set X);
  
  open_full_set : In (Ensemble X) topology set;
  
  intersection_stable : forall A B : Ensemble X,
    In (Ensemble X) topology A ->
    In (Ensemble X) topology B ->
    In (Ensemble X) topology (Intersection _ A B);
  
  union_stable : forall I : Type, forall (Ai : I -> Ensemble X),
    (forall i : I, In (Ensemble _) topology (Ai i)) ->
    In (Ensemble X) topology (Infinite_Union X I Ai)
}.

(** * Separation *)

Definition separated_space X set topology :=
 forall x y:X,
   In _ set x -> In _ set y ->
   (forall Ox Oy, In _ topology Ox -> In _ topology Oy -> In _ Ox x -> In _ Oy y -> 
      exists z, In _ Ox z /\ In _ Oy z)
   -> x = y.

(** * Sets properties *)

(* These lemmas probably have other names *)
(* They should be in MySets, but they probably are already *)
Lemma intersection_empty_set_absorbing_l :
  forall U:Type, forall A:Ensemble U,
  Intersection U (Empty_set U) A = Empty_set U.
intuition.
Qed.

Lemma intersection_empty_set_absorbing_r :
  forall U:Type, forall A:Ensemble U,
  Intersection U A (Empty_set U) = Empty_set U.
intuition.
Qed.

Lemma intersection_idempotent :
  forall U:Type, forall A:Ensemble U,
  Intersection U A A = A.
intros U A.
apply Extensionality_Ensembles.
unfold Same_set; split; intuition.
Qed.



(** * Infinite_Union Properties*)

Lemma subsets_stable_by_Infinite_Union :
  forall (U : Type) (I : Type) (Ai : I -> Ensemble U) (B : Ensemble U),
    (forall i:I, Included U (Ai i) B) ->
    Included U (Infinite_Union U I Ai) B.
intros U I Ai B HAi x HIU.
destruct HIU.
elim H; intros i HxAi.
apply (HAi i); assumption.
Qed.

Lemma Infinite_Union_absorbs_subset :
  forall (U : Type) (I : Type) (Ai : I -> Ensemble U) (B : Ensemble U),
    (exists i:I, Included U B (Ai i)) ->
    Included U B (Infinite_Union U I Ai).
intros U I Ai B HAi.
elim HAi.
intros i HIi x HxB.
apply Infinite_Union_intro; exists i.
apply HIi; assumption.
Qed.

Lemma effective_empty : forall (U:Type) (A:Ensemble U),
  (forall x:U, ~ In U A x) -> A = Empty_set U.
intros U A Nox.
apply Extensionality_Ensembles.
split.

intros x HxA.
  apply False_ind.
  apply (Nox x); assumption.
  
intros x Hxnowhere.
induction Hxnowhere.
Qed.






(** * Trivial topology *)

Section Trivial_Topology.

  Variable U : Type.
  Variable set : Ensemble U.

  Definition trivial := (Couple (Ensemble U) (Empty_set U) set).

  Definition open e := In (Ensemble U) trivial e.

  Fact trivial_open_empty_set : open (Empty_set U).
  apply Couple_l.
  Qed.

  Fact trivial_open_full_set : open set.
  apply Couple_r.
  Qed.

  Fact trivial_intersection_stable : forall A B : Ensemble U,
    open A -> open B -> open (Intersection U A B).
  intros A B OA OB.
  induction OA.
  rewrite intersection_empty_set_absorbing_l.
  apply Couple_l.
  induction OB.
  rewrite intersection_empty_set_absorbing_r.
  apply Couple_l.
  rewrite intersection_idempotent.
  apply Couple_r.
  Qed.

  Lemma open_included_in_set : forall A, open A -> Included U A set.
  intros A OA.
  destruct OA; intuition.
  Qed.
  
  (* excluded_middle is used because of undecidability of Type *)
  Require Import ClassicalFacts.
  
  Lemma disjonction_exists : excluded_middle -> forall (X:Type) (P:X->Prop),
    (exists x:X, P x) \/ (forall x:X, ~ P x).
  intros EM X P.
  elim (EM (exists x, P x)).
  left; assumption.
  right.
    intros x Px.
    apply H.
    exists x; assumption.
  Qed.
  
  (* begin hide *)
  Lemma eq_imply : forall X (P:X->Prop) A x, P x -> A = x -> P A.
  intros X P A x Px Eax; rewrite Eax; exact Px.
  Qed.
  (* end hide *)
  Fact trivial_union_stable : excluded_middle ->
    forall (I:Type) (Ai:I -> Ensemble U),
     (forall i : I, open (Ai i)) -> open (Infinite_Union U I Ai).
  
  intros EM I Ai OAi.
  assert (DISJ :
    (exists x : U,   In U (Infinite_Union U I Ai) x) \/
    (forall x : U, ~ In U (Infinite_Union U I Ai) x)   ).
   apply (disjonction_exists EM).
   
   elim DISJ; clear DISJ.
    intros Hexists; elim Hexists; intros x Hx.
    assert (exists i : _, In U (Ai i) x) as Geti.
     inversion Hx; assumption.
     
     elim Geti; intros i HxAi.
     assert (Ai i = set).
    assert (Ai i = set \/ Ai i = Empty_set U) as HAi.
     assert (open (Ai i)).
      apply OAi.
      
      inversion H.
       right; reflexivity.
       
       left; reflexivity.
       
     elim HAi.
      trivial.
      
      intro Hinv; rewrite Hinv in HxAi; inversion HxAi.
    
    assert (EqUnion : Infinite_Union U I Ai = set).
     apply Extensionality_Ensembles.
     split.
      apply subsets_stable_by_Infinite_Union.
      intros i0.
      apply open_included_in_set.
      apply OAi.
      
      apply (Infinite_Union_absorbs_subset U I Ai).
      exists i; rewrite H in |- *; intuition.
      
     rewrite EqUnion in |- *.
     apply Couple_r.
     
    intros Hfn.
    apply (effective_empty U (Infinite_Union U I Ai)) in Hfn.
    rewrite Hfn in |- *.
    constructor.
  Qed.

  Parameter EM : excluded_middle.
  
  Instance trivial_topology : Topological_Space U set trivial := {
    open_empty_set := trivial_open_empty_set;
    open_full_set := trivial_open_full_set;
    intersection_stable := trivial_intersection_stable;
    union_stable := (trivial_union_stable EM)
  }.
End Trivial_Topology.









(** * Discrete topology *)

Section Discrete_Topology.
  
  Variable U : Type.
  Variable set : Ensemble U.
  
  Definition discrete := Power_set U set.
  
  Definition part e := In (Ensemble U) discrete e.
  
  Fact discrete_open_empty_set : part (Empty_set U).
  apply Definition_of_Power_set.
  intuition.
  Qed.

  Fact discrete_open_full_set : part set.
  apply Definition_of_Power_set.
  intuition.
  Qed.

  Fact discrete_intersection_stable : forall A B : Ensemble U,
    part A -> part B -> part (Intersection U A B).
  intros A B pA _.
  apply Definition_of_Power_set.
  intros x xI.
  destruct xI; clear H0.
  destruct pA.
  apply H0.
  assumption.
  Qed.

  Fact discrete_union_stable : forall I : Type, forall Ai : I -> Ensemble U,
   (forall i : I, part (Ai i)) -> part (Infinite_Union U I Ai).
  intros I Ai pAi.
  
  apply  Definition_of_Power_set.
  apply subsets_stable_by_Infinite_Union.
  intros i x HxAi.
  assert (Included U (Ai i) set).
    assert (part (Ai i)).
      apply pAi.
    destruct H; assumption.
  
  unfold Included in * |-  .
  apply H; assumption.
  Qed.
  
  Instance discrete_topology : Topological_Space U set discrete := {
    open_empty_set := discrete_open_empty_set;
    open_full_set := discrete_open_full_set;
    intersection_stable := discrete_intersection_stable;
    union_stable := discrete_union_stable
  }.
End Discrete_Topology.


