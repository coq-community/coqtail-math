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

Require Export Ensembles.

Section Ensembles.

Variable U : Type.

Lemma Union_comm : forall X Y:Ensemble U, Union U X Y=Union U Y X.
Proof.
intros.
apply Extensionality_Ensembles.
split.
intro. intros.
destruct H.
apply Union_intror.
auto.
apply Union_introl.
auto.
intro. intros.
destruct H.
apply Union_intror.
auto.
apply Union_introl.
auto.
Qed.

Lemma Intersection_comm : forall X Y:Ensemble U, 
  Intersection U X Y=Intersection U Y X.
Proof.
intros.
apply Extensionality_Ensembles.
split.
intro. intros.
destruct H.
split.
auto.
auto.
intro. intros.
destruct H.
split.
auto.
auto.
Qed.

Lemma Union_empty_set_left : forall X:Ensemble U,
  Union U (Empty_set U) X=X.
Proof.
intros.
apply Extensionality_Ensembles.
split.
intro. intros.
destruct H.
inversion H.
auto.
intro. intros.
apply Union_intror.
auto.
Qed.

Lemma Union_empty_set_right : forall X:Ensemble U,
  Union U X (Empty_set U)=X.
Proof.
intros.
apply Extensionality_Ensembles.
split.
intro. intros.
destruct H.
auto.
inversion H.
intro. intros.
apply Union_introl.
auto.
Qed.

Lemma Union_assoc : forall X Y Z:Ensemble U,
  Union U (Union U X Y) Z=Union U X (Union U Y Z).
Proof.
intros.
apply Extensionality_Ensembles.
split.
intro. intros.
destruct H. destruct H.
apply Union_introl. auto.
apply Union_intror. apply Union_introl. auto.
apply Union_intror. apply Union_intror. auto.

intro. intros.
destruct H.
apply Union_introl. apply Union_introl. auto.
destruct H.
apply Union_introl. apply Union_intror. auto.
apply Union_intror. auto.
Qed.

Lemma Union_add_left : forall X Y:Ensemble U, forall x:U,
  Union U (Add U X x) Y=Add U (Union U X Y) x.
Proof.
intros.
unfold Add.
replace (Union U X (Singleton U x)) with (Union U (Singleton U x) X).
rewrite Union_assoc.
rewrite Union_comm.
auto.
apply Union_comm.
Qed.

Lemma Union_add_right : forall X Y:Ensemble U, forall x:U,
  Union U Y (Add U X x)=Add U (Union U Y X) x.
Proof.
intros.
replace (Union U Y X) with (Union U X Y).
rewrite <- Union_add_left.
apply Union_comm.
apply Union_comm.
Qed.

Lemma Disjoint_downward_closed : forall X Z:Ensemble U,
  Disjoint U X Z -> forall Y:Ensemble U, 
  Included U Y X -> Disjoint U Y Z.
Proof.
intros.
constructor.
intros.
intro.
destruct H.
destruct H1.
apply H with x.
constructor.
auto.
auto.
Qed.

Lemma included_in_union : forall X Y:Ensemble U,
  Included U X (Union U X Y).
Proof.
intros. intro. intros.
apply Union_introl.
auto.
Qed.

Lemma Singleton_is_add_empty : forall x:U, Singleton U x=Add U (Empty_set U) x.
Proof.
intros.
unfold Add.
rewrite Union_empty_set_left.
auto.
Qed.

End Ensembles.
