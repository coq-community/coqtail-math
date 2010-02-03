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
Require Export Nk_ind.
Require Export Ndiv.
Open Scope nat_scope.

(** * Definition of a finite sum on [nat] with an index starting from 0 *)

Fixpoint Nfinite_sum_0_n (n : nat) (f : nat -> nat) {struct n} : nat :=
match n with
| 0 => f 0
| S n' => (f n) + Nfinite_sum_0_n n' f
end.

(** * Properties of finite sum *)

(** Compatibility with sum *)
Lemma Nfinite_sum_plus_compat : forall n f g,
  Nfinite_sum_0_n n f + Nfinite_sum_0_n n g = Nfinite_sum_0_n n (fun k => f k + g k).
Proof.
induction n.
compute. reflexivity.
intros.
unfold Nfinite_sum_0_n. fold Nfinite_sum_0_n.
rewrite plus_assoc_reverse.
rewrite plus_assoc_reverse.
assert (g (S n) + Nfinite_sum_0_n n g = Nfinite_sum_0_n n g + g (S n)).
auto with arith.
rewrite H.
clear H.
assert (Nfinite_sum_0_n n f + (Nfinite_sum_0_n n g + g (S n)) =
  Nfinite_sum_0_n n f + Nfinite_sum_0_n n g + g (S n)).
auto with arith.
rewrite H.
clear H.
rewrite IHn.
auto with arith.
Qed.

(** Distributivity of multiplication *)
Lemma Nfinite_sum_mult_distrib : forall a n f, 
  a * Nfinite_sum_0_n n f = Nfinite_sum_0_n n (fun k => a * f k).
Proof.
induction n.
compute. reflexivity.
intros.
unfold Nfinite_sum_0_n. fold Nfinite_sum_0_n.
rewrite <- IHn.
ring.
Qed.

(** Compatibility with equality (limited equality) *)
Lemma Nfinite_sum_subtle_eq_compat :
  forall n f g, (forall k, k <= n -> f k = g k) -> Nfinite_sum_0_n n f = Nfinite_sum_0_n n g.
Proof.
induction n.
compute. intros.
apply H. trivial.
intros.
unfold Nfinite_sum_0_n. fold Nfinite_sum_0_n.
rewrite (IHn f g).
rewrite (H (S n)).
reflexivity.
trivial.
intros.
apply H.
auto with arith.
Qed.

(** compatibility with equality (unlimited equality) *)
Lemma Nfinite_sum_eq_compat : forall n f g, 
  (forall k, f k = g k) -> Nfinite_sum_0_n n f = Nfinite_sum_0_n n g.
Proof.
intros.
apply Nfinite_sum_subtle_eq_compat.
intros.
apply H.
Qed.

(** One term, lower splitting of finite sum *)
Lemma Nfinite_sum_split_lower : forall n f,
  Nfinite_sum_0_n (S n) f = f 0 + Nfinite_sum_0_n n (fun k => f (S k)).
Proof.
induction n.
compute. auto with arith.
intros.
unfold Nfinite_sum_0_n. fold Nfinite_sum_0_n.
unfold Nfinite_sum_0_n in IHn. fold Nfinite_sum_0_n in IHn.
rewrite IHn.
rewrite plus_assoc.
rewrite plus_assoc.
auto with arith.
Qed.

(** One term, upper splitting of finite sum *)
Lemma Nfinite_sum_split_upper : forall n f,
  Nfinite_sum_0_n (S n) f = Nfinite_sum_0_n n f + f (S n).
Proof.
intros.
unfold Nfinite_sum_0_n. fold Nfinite_sum_0_n.
auto with arith.
Qed.

(** General splitting of finite sum *)
Lemma Nfinite_sum_split : forall n p q f, 
  p + q = n -> Nfinite_sum_0_n (S n) f = Nfinite_sum_0_n p f + Nfinite_sum_0_n q (fun k => f (kth_S p k)).
Proof.
induction n.
induction p.
intros.
simpl in H.
rewrite H.
unfold Nfinite_sum_0_n.
unfold kth_S.
auto with arith.

intros.
discriminate H.

destruct p.
intros.
simpl in H.
rewrite H. clear H.
assert (Nfinite_sum_0_n 0 f=f 0).
compute. reflexivity.
rewrite H. clear H.
rewrite Nfinite_sum_split_lower.
unfold kth_S.
reflexivity.
intros.
assert (p+q=n).
auto with arith.
clear H.
assert (Nfinite_sum_0_n (S (S n)) f=f(S(S n))+Nfinite_sum_0_n (S n) f).
rewrite plus_comm.
apply Nfinite_sum_split_upper.
rewrite H. clear H.
rewrite (IHn p q).
rewrite Nfinite_sum_split_upper.
assert (f (S p) + Nfinite_sum_0_n q (fun k : nat => f (kth_S (S p) k))
  = Nfinite_sum_0_n (S q) (fun k=>f(kth_S p k))).
rewrite Nfinite_sum_split_lower.
rewrite kth_S_special.
unfold kth_S. fold kth_S.
assert (forall k:nat, kth_S p (S k)=S(kth_S p k)).
intro.
rewrite kth_S_sym.
unfold kth_S. fold kth_S.
rewrite kth_S_sym.
reflexivity.
assert (Nfinite_sum_0_n q (fun k : nat => f (S (kth_S p k)))=
  Nfinite_sum_0_n q (fun k : nat => f (kth_S p (S k)))).
apply Nfinite_sum_eq_compat.
intro.
rewrite (H k).
reflexivity.
rewrite H1.
reflexivity.
assert (Nfinite_sum_0_n p f + f (S p) +
  Nfinite_sum_0_n q (fun k : nat => f (kth_S (S p) k))
  =
  Nfinite_sum_0_n p f + (f (S p) +
  Nfinite_sum_0_n q (fun k : nat => f (kth_S (S p) k)))).
auto with arith.
rewrite H1. clear H1.
rewrite H. clear H.
assert (f (S (S n)) +
  (Nfinite_sum_0_n p f + Nfinite_sum_0_n q (fun k : nat => f (kth_S p k)))
  =
  Nfinite_sum_0_n p f + (Nfinite_sum_0_n q (fun k : nat => f (kth_S p k))+f (S (S n)))).
rewrite plus_comm.
auto with arith.
rewrite H. clear H.
assert (Nfinite_sum_0_n (S q) (fun k : nat => f (kth_S p k)) =
  Nfinite_sum_0_n q (fun k : nat => f (kth_S p k)) + f (S (S n))).
rewrite Nfinite_sum_split_upper.
assert (kth_S p (S q)=S(S n)).
rewrite kth_S_sym.
unfold kth_S. fold kth_S.
rewrite kth_S_sym.
rewrite kth_S_plus.
assert (q+p+1=(p+q)+1).
auto with arith.
rewrite H. rewrite H0. clear H.
rewrite plus_1_r.
reflexivity.
rewrite <- H.
reflexivity.
rewrite H.
auto with arith.
exact H0.
Qed.

(** Compatibility with division *)
Lemma Nfinite_sum_div_compat : forall n f p,
  (forall k, k <= n -> (p | f k)) -> (p | Nfinite_sum_0_n n f).
Proof.
induction n.
intros.
simpl. apply H. auto.
intros.
rewrite Nfinite_sum_split_upper.
apply Ndiv_plus_compat.
apply IHn.
intros.
apply H. auto with arith.
apply H.
auto.
Qed.
