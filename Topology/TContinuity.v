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

Require Import Reals.
Require Import Ensembles.
Require Import Topology.
Require Import Functions.
Require Import Metrics.
Require Import TFunctions.

Definition Topological_Continuity
  (U:Type) (V:Type)
  (A:Ensemble U) (B:Ensemble V)
  (TA:Ensemble (Ensemble U)) (TB:Ensemble (Ensemble V))
  (TopA : Topological_Space U A TA) (TopB : Topological_Space V B TB)
  (f : U->V) : Prop := function U V A B f ->
  forall OB, In _ TB OB -> In _ TA (Intersection _ (Preimage _ _ OB f) A).

Open Scope R_scope.

Definition Metric_Continuity_Pt
  (U:Type) (V:Type)
  (dU : U -> U -> R) (dV : V -> V -> R)
  (MU : Metric_Space U dU) (MV : Metric_Space V dV)
  (f : U->V) (a : U) : Prop :=
    forall eps:R, 0<eps ->
    exists delta:R, 0<delta /\
      forall a',
      dU a a' < delta ->
      dV (f a) (f a') < eps.

Definition Metric_Continuity
  (U:Type) (V:Type)
  (dU : U -> U -> R) (dV : V -> V -> R)
  (MU : Metric_Space U dU) (MV : Metric_Space V dV)
  (f : U->V) : Prop :=
    forall a, Metric_Continuity_Pt U V dU dV MU MV f a.

Lemma metric_continuity_is_topological
  (U:Type) (V:Type)
  (dU : U -> U -> R) (dV : V -> V -> R)
  (MU : Metric_Space U dU) (MV : Metric_Space V dV)
  (f : U->V) :
    Metric_Continuity U V dU dV MU MV f ->
    Topological_Continuity U V (Full_set U) (Full_set V)
      (metric_open _ dU) (metric_open _ dV)
      (metric_space_topological _ _) (metric_space_topological _ _)
      f.
Proof.
intros U V dU dV MU MV f HMC Hfun O openO x Hx.
assert (Intersection U (Preimage U V O f) (Full_set U) = Preimage U V O f).
 apply Extensionality_Ensembles; split; auto with sets.
 intros t Ht; split; auto; constructor.
rewrite H in Hx; rewrite H; clear H.
destruct openO with (f x) as [e [epos He]]; destruct Hx; subst; auto.
destruct (HMC x e epos) as [d [dpos Hd]].
exists d.
split; auto.
intros y Hxy.
pose proof He (f y) (Hd y Hxy).
econstructor; auto; auto.
Qed.
