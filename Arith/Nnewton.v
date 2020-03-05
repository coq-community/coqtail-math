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
Require Import Compare.
Require Export Nbinomial.
Require Export Ndiv.
Require Export Npow.
Require Export Nfinite_sum.
Open Scope nat_scope.

(** * Definition of a newton sum *)
Definition Nnewton_sum n a b : nat :=
  Nfinite_sum_0_n n (fun k => (Nbinomial n k) * (a ^ k) * (b ^ (n - k))).

(** * Newton sum theorem *)
Theorem Nnewton : forall n a b,
  (a + b) ^ n = Nnewton_sum n a b.
Proof.
(* the coq proof is highly technical whereas the mathematical proof is stupid *)
induction n.
compute.
reflexivity.
intros.
rewrite Npower_succ.
rewrite mult_plus_distr_r.
rewrite IHn.
unfold Nnewton_sum.
rewrite Nfinite_sum_mult_distrib.
assert (forall k, a * (Nbinomial n k * a ^ k * b ^ (n - k))=
  (Nbinomial n k * a ^ (S k) * b ^ (n - k))).
intro.
assert (a * (Nbinomial n k * a ^ k * b ^ (n - k)) =
Nbinomial n k * (a * a ^ k) * b ^ (n - k)).
ring.
rewrite H.
rewrite Npower_succ.
reflexivity.
assert (Nfinite_sum_0_n n (fun k : nat => a * (Nbinomial n k * a ^ k * b ^ (n - k))) =
  Nfinite_sum_0_n n (fun k : nat => (Nbinomial n k * a ^(S k) * b ^ (n - k)))).
apply Nfinite_sum_eq_compat.
exact H.
rewrite H0. clear H0.
rewrite Nfinite_sum_mult_distrib.
assert (forall k:nat, b * (Nbinomial n k * a ^ k * b ^ (n - k)) =
  Nbinomial n k * a ^ k * b ^ (S (n - k))).
intro.
assert (b * (Nbinomial n k * a ^ k * b ^ (n - k)) =
Nbinomial n k * (a ^ k) * (b * b ^ (n - k))).
ring.
rewrite H0.
rewrite Npower_succ.
reflexivity.
assert (Nfinite_sum_0_n n (fun k : nat => b * (Nbinomial n k * a ^ k * b ^ (n - k))) =
  Nfinite_sum_0_n n (fun k : nat => (Nbinomial n k * a ^k)* b ^ (S (n - k)))).
apply Nfinite_sum_eq_compat.
exact H0.
rewrite H1.
clear H1. clear H0. clear H. clear IHn.

rewrite Nfinite_sum_split_lower.
simpl.
rewrite plus_0_r.
assert (Nfinite_sum_0_n n
  (fun k : nat => Nbinomial (S n) (S k) * a ^ S k * b ^ (n - k)) =
  Nfinite_sum_0_n n
  (fun k : nat => Nbinomial n (S k) * a ^ S k * b ^ (n - k) + 
    Nbinomial n k * a ^ S k * b ^ (n - k))).
apply Nfinite_sum_subtle_eq_compat.
intros.
rewrite <- Nbinomial_pascal.
ring.
exact H.
simpl in H.
rewrite H. clear H.
rewrite <- Nfinite_sum_plus_compat.

assert (b ^ S n +
  Nfinite_sum_0_n n (fun k : nat => Nbinomial n (S k) * a ^ S k * b ^ (n - k)) =
  Nfinite_sum_0_n (S n) (fun k : nat => Nbinomial n k * a ^ k * b ^ (S (n - k)))).
rewrite Nfinite_sum_split_lower.
rewrite Nbinomial_0.
simpl.
rewrite <- minus_n_O.
rewrite plus_0_r.
assert (Nfinite_sum_0_n n
  (fun k : nat => Nbinomial n (S k) * a ^ S k * b ^ (n - k)) =
  Nfinite_sum_0_n n
  (fun k : nat => Nbinomial n (S k) * a ^ S k * b ^ S (n - S k))).
apply Nfinite_sum_subtle_eq_compat.
intros.
apply le_le_S_eq in H.
destruct H.
intros.
assert (S(n-S k)=n-k).
induction n.
apply le_Sn_O in H.
contradiction.
apply le_le_S_eq in H.
destruct H.
rewrite <- minus_Sn_m.
rewrite IHn.
apply  minus_Sn_m.
apply le_S_n.
auto with arith.
apply le_S_n.
auto with arith.
apply le_S_n.
auto with arith.
apply eq_eq_nat in H.
unfold eq_nat in H.
apply eq_nat_eq in H.
rewrite H.
rewrite minus_diag.
rewrite <- minus_Sn_m.
rewrite minus_diag.
reflexivity.
auto with arith.
rewrite H0.
reflexivity.
rewrite H.
rewrite Nbinomial_outside.
simpl.
reflexivity.
auto with arith.
simpl in H.
rewrite H. clear H.
reflexivity.

assert (b ^ S n +
 (Nfinite_sum_0_n n (fun k : nat => Nbinomial n (S k) * a ^ S k * b ^ (n - k)) +
  Nfinite_sum_0_n n (fun k : nat => Nbinomial n k * a ^ S k * b ^ (n - k)))
  =
  (b ^ S n + Nfinite_sum_0_n n (fun k : nat => Nbinomial n (S k) * a ^ S k * b ^ (n - k)) +
  (Nfinite_sum_0_n n (fun k : nat => Nbinomial n k * a ^ S k * b ^ (n - k))))).
rewrite plus_assoc.
auto with arith.
simpl in H0, H.
rewrite H0. clear H0.
rewrite H. clear H.

assert (Nfinite_sum_0_n n (fun k : nat => Nbinomial n k * a ^ k * b ^ S (n - k)) =
  Nfinite_sum_0_n (S n) (fun k : nat => Nbinomial n k * a ^ k * b ^ S (n - k))).
rewrite Nfinite_sum_split_upper.
rewrite Nbinomial_outside.
simpl.
auto with arith.
auto with arith.
rewrite Nbinomial_outside; auto.
ring.
Qed.
