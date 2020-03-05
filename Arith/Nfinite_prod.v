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
Require Export Nk_ind.
Require Export Npow.
Require Export Ndiv.
Open Scope nat_scope.

(** * Definition of a finite product on [nat] with an index starting from 0 *)
Fixpoint Nfinite_prod_0_n (n:nat) (f:nat -> nat) {struct n} : nat :=
match n with
| 0 => f 0
| S n' => (Nfinite_prod_0_n n' f) * (f n)
end.

(** * Properties of finite product *)
(** Compatibility with equality (limited equality) *)
Lemma Nfinite_prod_subtle_eq_compat : forall n f g,
  (forall k, k <= n -> f k = g k) -> Nfinite_prod_0_n n  f= Nfinite_prod_0_n n g.
Proof.
induction n.
compute. intros.
apply H. trivial.
intros.
unfold Nfinite_prod_0_n. fold Nfinite_prod_0_n.
rewrite (IHn f g).
rewrite (H (S n)).
reflexivity.
trivial.
intros.
apply H.
auto with arith.
Qed.

(** Compatibility with equality (unlimited equality) *)
Lemma Nfinite_prod_eq_compat : forall n f g,
  (forall k, f k = g k) -> Nfinite_prod_0_n n f = Nfinite_prod_0_n n g.
Proof.
intros.
apply Nfinite_prod_subtle_eq_compat.
intros.
apply H.
Qed.

(** One term, upper splitting of finite product *)
Lemma Nfinite_prod_split_upper : forall n f,
  Nfinite_prod_0_n (S n) f = (Nfinite_prod_0_n n f) * (f (S n)).
Proof.
unfold Nfinite_prod_0_n. fold Nfinite_prod_0_n.
reflexivity.
Qed.

(** One term, lower splitting of finite product *)
Lemma Nfinite_prod_split_lower : forall n f,
  Nfinite_prod_0_n (S n) f = (f 0) * (Nfinite_prod_0_n n (fun k => f (S k))).
Proof.
induction n.
intros.
unfold Nfinite_prod_0_n.
reflexivity.
intros.
rewrite Nfinite_prod_split_upper.
rewrite IHn.
rewrite Nfinite_prod_split_upper.
ring.
Qed.

(** Compatibility with multiplication *)
Lemma Nfinite_prod_mult_compat : forall n f a g,
  (forall k, k <= n -> f k = a * g k) -> Nfinite_prod_0_n n f = a^(S n) * Nfinite_prod_0_n n g.
Proof.
induction n.
intros.
unfold Nfinite_prod_0_n.
unfold Nat.pow.
rewrite mult_1_r.
apply H.
auto with arith.
intros.
rewrite Nfinite_prod_split_upper.
rewrite Nfinite_prod_split_upper.
rewrite H.
rewrite IHn with f a g.
rewrite Npower_succ.
rewrite Npower_succ.
rewrite Npower_succ.
ring.
intros.
apply H.
auto with arith.
auto with arith.
Qed.

(** 0 is absorbant *)
Lemma Nfinite_prod_0_absord : forall n f k,
  k <= n -> f k = 0 -> Nfinite_prod_0_n n f = 0.
Proof.
induction n.
intros.
compute.
apply le_n_O_eq in H.
rewrite <- H in H0.
exact H0.

intros.
rewrite Nfinite_prod_split_upper.
apply le_le_S_eq in H.
destruct H.
rewrite IHn with f k.
ring.
auto with arith.
exact H0.
rewrite <- H.
rewrite H0.
ring.
Qed.

(** Factorial is a finite product *)
Lemma Nfactorial_is_finite_prod : forall n,
  fact (S n) = Nfinite_prod_0_n n (fun k => S k).
Proof.
induction n.
compute. reflexivity.
assert (fact (S(S n))=S(S n)*fact(S n)).
compute. reflexivity.
rewrite H. clear H.
rewrite Nfinite_prod_split_upper.
rewrite IHn.
ring.
Qed.

(** Index reversal *)
Lemma Nfinite_prod_index_reversal : forall n f,
  Nfinite_prod_0_n n f = Nfinite_prod_0_n n (fun k => f(n - k)).
Proof.
induction n.
compute. reflexivity.
intros.
rewrite Nfinite_prod_split_upper.
rewrite Nfinite_prod_split_lower.
rewrite IHn.
rewrite <- minus_n_O.
assert (Nfinite_prod_0_n n (fun k : nat => f (S n - S k)) =
  Nfinite_prod_0_n n (fun k : nat => f (n - k))).
apply Nfinite_prod_subtle_eq_compat.
intros.
assert (S n-S k=n-k).
auto with arith.
rewrite H0. reflexivity.
rewrite H.
ring.
Qed.

(** Divisibility of finite product *)
Lemma Nfinite_prod_div : forall n f k p,
  k <= n -> (p | f k) -> (p | Nfinite_prod_0_n n f).
Proof.
induction n.
intros.
inversion H.
rewrite H1 in * |- *.
simpl. auto.
intros.
apply le_le_S_eq in H.
destruct H.
apply le_S_n in H.
simpl.
apply Ndiv_mult_compat.
apply IHn with k.
auto. auto.
simpl.
rewrite mult_comm.
apply Ndiv_mult_compat.
rewrite <- H.
auto.
Qed.
