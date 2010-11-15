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

(** * Topological space *)

Require Import Reals.
Require Import Ensembles.
Require Import Topology.
Require Import Fourier.

(** * Metric Space *)

Class Metric_Space
  (X : Type)
  (d : X -> X -> R)
:= {
  metric_pos : forall x y, (0 <= d x y)%R;
  metric_sym : forall x y, d x y = d y x;
  metric_refl : forall x y, (d x y = 0 <-> x = y)%R;
  metric_tri : forall x y z, (d x y <= d x z + d z y)%R
}.

(** * Open sets *)

Section Open_sets.
  Variable X : Type.
  Variable d : X -> X -> R.
  
  Open Scope R_scope.
  
  Definition metric_open W: Prop :=
    forall x, In _ W x -> exists eps:R, 0 < eps /\
    forall y, d x y < eps -> In _ W y.
  
End Open_sets.

(** * Balls *)

Section Balls.
  Variable X : Type.
  Variable d : X -> X -> R.
  Variable E : Metric_Space X d.
  
  Inductive open_ball c r (rpos : (0 < r)%R) : Ensemble X :=
    open_ball_intro : forall x, (d x c < r)%R -> In _ (open_ball c r rpos) x.
  
  Inductive closed_ball c r (rpos : (0 < r)%R) : Ensemble X :=
    closed_ball_intro : forall x, (d x c <= r)%R -> In _ (closed_ball c r rpos) x.
  
  Lemma open_ball_is_open : forall c r rpos, metric_open X d (open_ball c r rpos).
  Proof.
  intros c r rpos x Hx.
  destruct Hx as [x Hxc].
  exists (r - d x c)%R; split.
   apply Rlt_Rminus; auto.
   
   intros y Hxy.
   constructor.
   eapply Rle_lt_trans.
    apply (metric_tri _ _ x).
    
    rewrite (metric_sym y x); fourier.
  Qed.
End Balls.

(** * A metric space defines a topology *)

Section Metric_topology.
  Variable X : Type.
  Variable d : X -> X -> R.
  
  Fact metric_open_empty_set : metric_open X d (Empty_set _).
  intros x H.
  inversion H.
  Qed.
  
  Fact metric_open_full_set : metric_open X d (Full_set _).
  intros x _.
  exists 1%R.
  split. intuition.
  intros y _.
  constructor.
  Qed.
  
  Fact metric_intersection_stable : forall A B : Ensemble _,
    metric_open X d A -> metric_open X d B ->
    metric_open X d (Intersection _ A B).
  intros A B OA OB.
  intros x [y yA yB].
  elim (OA y). intros epsa [epsapos opena].
  elim (OB y). intros epsb [epsbpos openb].
  exists (Rmin epsa epsb).
  split.
    apply Rmin_Rgt_r.
    split; assumption.
  intros x' inx'.
  apply Rmin_Rgt_l in inx' as [ax' bx'].
  apply Intersection_intro;
    [apply opena | apply openb];
    apply Rgt_lt; assumption.
  assumption.
  assumption.
  Qed.
  
  Fact metric_union_stable : forall I : Type, forall Ai : I -> Ensemble _,
   (forall i : I, metric_open X d (Ai i)) -> metric_open X d (Infinite_Union _ I Ai).
  intros I Ai openAi.
  intros x xinU.
  induction xinU.
  elim H. intros i inxAi.
  elim (openAi i x).
  intros eps [epspos B].
  exists eps.
  split.
    exact epspos.
    intros y yinB.
  exists. exists i.
  apply (B _ yinB).
  assumption.
  Qed.
  
  Instance metric_space_topological : Topological_Space _ (Full_set _) (metric_open X d) := {
    open_empty_set := metric_open_empty_set;
    open_full_set := metric_open_full_set;
    intersection_stable := metric_intersection_stable;
    union_stable := metric_union_stable
  }.
End Metric_topology.

(** * A metric space is separated *)

Lemma metric_space_is_separated : forall X d (MX : Metric_Space X d),
  separated_space X (Full_set X) (metric_open X d).
Proof.
intros X d MX x y _ _ H.
apply (proj1 (metric_refl _ _)).
destruct (Rtotal_order (d x y) 0%R) as [|[|]]; auto.
 apply RIneq.Rle_not_lt in H0.
  contradiction.
  apply metric_pos.
 pose (d x y / 2)%R as r.
 assert (rpos : 0 < r).
  unfold r; fourier.
 pose (fun c => open_ball X d c r rpos) as ball.
 assert (centerinball : forall x, ball x x).
  constructor.
  rewrite (proj2 (metric_refl _ _)); auto.
 destruct (H (ball x) (ball y)
  (open_ball_is_open _ _ _ _ _ _)
  (open_ball_is_open _ _ _ _ _ _)
  (centerinball _)
  (centerinball _)) as [z []].
 destruct H1 as [z H1].
 destruct H2 as [z H2].
 unfold r in *.
 assert (d x y < d x y).
  apply Rle_lt_trans with (d z x + d z y).
   rewrite metric_sym with z x; apply metric_tri.
   
   replace (d x y) with (d x y / 2 + d x y / 2) by field.
   apply Rplus_lt_compat; auto.
 apply Rlt_irrefl in H3.
 contradiction.
Qed.
