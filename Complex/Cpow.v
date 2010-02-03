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

Require Export Cbase.
Require Import Omega.

Open Scope C_scope.

(** * Power definition on C *)

Fixpoint Cpow (z : C) (n : nat) {struct n} : C  :=
match n with
| 0%nat => 1
| S m => z * (Cpow z m)
end.

Infix "^" := Cpow : C_scope.

(** Rewrite lemmas on Cpow *)

Lemma Cpow_0 : forall z, z ^ 0 = 1. 
Proof.
auto with complex.
Qed.

Lemma C0_pow : forall n, (0 < n)%nat -> 0 ^ n = 0.
Proof.
intros n n_lb ; induction n.
 inversion n_lb.
 simpl.
 destruct (0 ^ n) ; CusingR_f.
Qed.

Lemma Cpow_S : forall (z : C) (n : nat), z ^ (S n) = z ^ n * z.
Proof.
intros. simpl. intuition.
Qed.

Lemma Cpow_add : forall (z : C) (n m : nat), z ^ (n + m) = z ^ n * z ^ m.
Proof.
intros z n m.
induction n.
 auto with complex.
replace (z ^ (S n + m)%nat) with (z * z ^ (n+m)%nat).
 rewrite IHn. replace (z ^ S n) with (z * (z ^ n)).
  auto with complex.
 destruct n ; simpl ; auto with complex.
replace (S n + m)%nat with (S (n + m))%nat.
 destruct n; destruct m ; simpl ; auto with complex.
simpl ; reflexivity.
Qed.

Lemma Cpow_mul : forall z n m, z ^ (n * m) = (z ^ n) ^ m.
Proof.
intros z n m ; induction m.
 rewrite mult_0_r ; reflexivity.
 simpl ; rewrite <- IHm ; rewrite <- Cpow_add ;
 replace (n * S m)%nat with (n + n * m)%nat by ring ; reflexivity.
Qed.

Lemma Cpow_mul_distr_l : forall z1 z2 n, (z1 * z2) ^ n = z1 ^ n * z2 ^ n.
Proof.
intros z1 z2 n; induction n.
  simpl; CusingR_f.
  repeat rewrite Cpow_S; rewrite IHn.
  rewrite Cmult_assoc.
  rewrite <- (Cmult_assoc (z2 ^ n) z1 z2).
  rewrite (Cmult_comm (z2 ^ n) z1).
  repeat rewrite Cmult_assoc.
  reflexivity.
Qed.

Lemma IRC_pow_compat : forall x n, IRC x ^ n = IRC (x ^ n).
Proof.
intros x n ; induction n.
 reflexivity.
 simpl ; rewrite IHn.
 CusingR_f.
Qed.	