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

Require Import Arith.
Require Export Ntools.
Require Export Nle.
Open Scope nat_scope.

(** * Definition of power over [nat] *)
(** Using the standard library's definition instead *)
Definition Npower := Nat.pow.

(** * Simplification *)

(** Simplification of [n ^ 1] *)
Lemma Npower_n_1: forall x, x ^ 1 = x.
Proof.
intros.
unfold Npower.
unfold iter_nat.
apply mult_1_r.
Qed.

(** Relation with successor *)
Lemma Npower_succ : forall a n, a ^ (S n) = a * a ^ n.
Proof.
intros.
unfold Npower. unfold iter_nat.
fold iter_nat. fold Npower.
reflexivity.
Qed.

(** Simplification of [1 ^ n] *)
Lemma Npower_1_n : forall n, 1 ^ n = 1.
Proof.
apply Nat.pow_1_l.
Qed.

(** Simplification of [0 ^ n] *)
Lemma Npower_0_n : forall n, n > 1 -> 0 ^ n = 0.
Proof.
destruct n.
intros.
inversion H.
intros.
compute.
auto.
Qed.

(** Simplification of [n ^ 0] *)
Lemma Npower_n_0 : forall n, n>1 -> n ^ 0 = 1.
Proof.
compute. auto.
Qed.

(** * Compatibility with order *)

(** Compatibility with addition and order *)
Lemma Npower_plus_le_compat : forall a b c, c > 0 -> (a + b) ^ c >= a ^ c + b ^ c.
Proof.
induction c.
intros.
inversion H.
intros.
rewrite Npower_succ.
rewrite mult_plus_distr_r.
apply plus_le_compat.
rewrite Npower_succ.
apply mult_le_compat_l.
destruct c.
compute. auto.
apply le_trans with (a^(S c)+b^(S c)).
auto with arith.
apply IHc.
auto with arith.

rewrite Npower_succ.
apply mult_le_compat_l.
destruct c.
compute. auto.
apply le_trans with (a^(S c)+b^(S c)).
auto with arith.
apply IHc.
auto with arith.
Qed.

(** Compatibility and order *)
Lemma Npower_le_compat_r : forall n p q, n > 0 -> p <= q -> n ^ p <= n ^ q.
Proof.
intros.
apply Nle_plus in H0.
destruct H0.
generalize x q H H0.
clear H H0. clear x q.
induction x.
intros.
rewrite plus_0_r in H0.
rewrite H0.
auto.

intros.
rewrite <- plus_Snm_nSm in H0.
simpl in H0.
rewrite H0.
rewrite Npower_succ.
replace (n^p) with (1*n^p).
apply mult_le_compat.
auto.
apply IHx.
auto.
auto.
ring.
Qed.

