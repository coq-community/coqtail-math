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

Require Import Plus.
Require Import Le.
Require Import Compare.
Open Scope nat_scope.

(* begin hide *)
Lemma plus_1_r : forall n, n+1=S n.
induction n.
auto with arith.
simpl.
rewrite IHn.
reflexivity.
Qed.
(* end hide *)

(** * Definition of kth-successor and generalized AND hypothesis *)

Fixpoint kth_S (k : nat) (n : nat) {struct k} : nat:=
match k with
| 0 => S n
| S k' => S(kth_S k' n)
end.

Fixpoint next_P_k (k : nat) (delta : nat) (P : nat -> Prop) {struct k} : Prop:=
match k with
| 0 => P delta
| S k' => P (kth_S delta k') /\ next_P_k k' delta P
end.

(** * Properties of [next_P_k] and [kth_S] *)
(** [next_P_k] upper weakening *)
Lemma next_P_k_strong : forall k delta P,
  next_P_k (S k) delta P -> next_P_k k delta P.
induction k.
intros.
unfold next_P_k.
unfold next_P_k in H.
destruct H.
exact H0.

intros.
unfold next_P_k. fold next_P_k.
unfold next_P_k in H. fold next_P_k in H.
destruct H.
destruct H0.
split.
exact H0.
exact H1.
Qed.

(** commutativity of nested [kth_S] *)
Lemma kth_S_comm : forall delta gamma n, 
  kth_S delta (kth_S gamma n) = kth_S gamma (kth_S delta n).
induction delta.
intros.
induction gamma.
compute. reflexivity.
unfold kth_S. fold kth_S.
unfold kth_S in IHgamma. fold kth_S in IHgamma.
rewrite IHgamma.
reflexivity.

intros.
unfold kth_S. fold kth_S.
rewrite IHdelta.
induction gamma.
compute. reflexivity.
unfold kth_S. fold kth_S.
rewrite IHgamma.
reflexivity.
Qed.

(** special case of [kth_S] *)
Lemma kth_S_special : forall k, kth_S k 0 = S k.
Proof.
induction k.
compute. reflexivity.
unfold kth_S. fold kth_S.
rewrite IHk.
reflexivity.
Qed.

(** [next_P_k] to [P] weakening *)
Lemma next_P_k_special: forall k delta P,
  next_P_k k delta P -> P delta.
Proof.
induction k.
intros. exact H.
intros. apply IHk.
apply next_P_k_strong.
exact H.
Qed.

(** symmetry of [kth_S] *)
Lemma kth_S_sym : forall k n, kth_S k n = kth_S n k.
Proof.
induction k.
intro.
rewrite kth_S_special.
reflexivity.

intro.
unfold kth_S. fold kth_S.
rewrite IHk.
induction n.
compute. reflexivity.
unfold kth_S. fold kth_S.
rewrite IHn.
reflexivity.
Qed.

(** relation between [kth_S] and [plus] *)
Lemma kth_S_plus : forall k n, kth_S k n = n + k + 1.
Proof.
induction k.
intro.
unfold kth_S.
rewrite plus_0_r.
rewrite plus_1_r.
reflexivity.
intro.
unfold kth_S. fold kth_S.
rewrite IHk.
assert (n + S k + 1=S k + n +1).
auto with arith.
rewrite H. clear H.
simpl.
auto with arith.
Qed.

(** introduction of [next_P_k] *)
Theorem next_P_k_correct : forall k delta, forall P : nat -> Prop,
  P delta -> (forall x, x < k -> P (kth_S delta x)) -> next_P_k k delta P.
Proof.
induction k.
intros.
simpl.
exact H.
intros.
simpl.
split.
apply H0.
auto with arith.
apply IHk.
exact H.
intros.
apply H0.
auto with arith.
Qed.

(** elimination of [next_P_k] *)
Theorem next_P_k_complete : forall k delta P,
  next_P_k k delta P -> P delta /\ (forall x, x < k -> P (kth_S delta x)).
Proof.
induction k.
intros.
split.
simpl in H.
auto.
intros.
inversion H0.
intros.
assert (P delta /\ forall x, x<k -> P(kth_S delta x)).
apply IHk.
apply next_P_k_strong.
auto.
split.
destruct H0.
auto.
intros.
apply le_le_S_eq in H1.
destruct H1.
apply H0.
auto with arith.
apply eq_add_S in H1.
rewrite H1.
simpl in H.
destruct H.
apply H.
Qed.

(** [next_P_k] lower weakening *)
Lemma next_P_k_strong2 : forall k delta P,
  next_P_k (S k) delta P -> next_P_k k (S delta) P.
Proof.
induction k.
intros.
unfold next_P_k. fold next_P_k.
unfold next_P_k in H. rewrite kth_S_special in H.
destruct H. exact H.

intros.
unfold next_P_k. fold next_P_k.
split.
unfold next_P_k in H. fold next_P_k in H.
unfold kth_S. fold kth_S.
destruct H.
rewrite kth_S_sym in H.
unfold kth_S in H. fold kth_S in H.
rewrite kth_S_sym in H.
exact H.
apply IHk.
unfold next_P_k in H. fold next_P_k in H.
destruct H.
exact H0.
Qed.

(** * Inductions on [nat] *)

(** Generalized n-step induction *)
Theorem nat_k_ind : forall k P,
  next_P_k k 0 P -> (forall n, P n -> P(kth_S k n)) -> forall n, P n.
Proof.
intros.
assert (forall n:nat, next_P_k (S k) n P).
apply nat_ind.
unfold next_P_k. fold next_P_k.
split.
unfold kth_S.
assert (kth_S k 0=S k).
apply kth_S_special.
rewrite <- H1.
apply H0.
apply next_P_k_special with k.
exact H.

exact H.

intros.
unfold next_P_k. fold next_P_k.
split.
rewrite kth_S_sym.
apply H0.
apply next_P_k_strong2 in H1.
apply next_P_k_special with k.
exact H1.
apply next_P_k_strong2.
exact H1.
destruct H1 with n.
fold next_P_k in H3.
apply next_P_k_special with k.
exact H3.
Qed.

(** Simple nat induction is a special case *)
Lemma nat_simple_ind : forall P : nat -> Prop, 
   P 0 -> (forall n:nat, P n -> P(S n)) -> forall n, P n.
Proof.
exact (nat_k_ind 0).
Qed.

(** Double-step nat induction is a special case *)
Lemma nat_double_ind : forall P : nat -> Prop, 
   P 0 -> P 1 -> (forall n, P n -> P(S(S n))) -> forall n, P n.
Proof.
intros P H0 H1 Hind.
apply nat_k_ind with 1.
compute.
split.
exact H1. exact H0.
exact Hind.
Qed.

(** Triple-step nat induction is a special case *)
Lemma nat_triple_ind : forall P : nat -> Prop, 
   P 0 -> P 1 -> P 2-> (forall n, P n -> P(S (S (S n)))) -> forall n, P n.
Proof.
intros P H0 H1 H2 Hind.
apply nat_k_ind with 2.
compute.
split.
exact H2. split.
exact H1. exact H0.
exact Hind.
Qed.

(** Strong induction on [nat] *)
Lemma nat_strong_ind : forall P : nat -> Prop,
  P 0 -> (forall n, (forall k, k<=n -> P k) -> P(S n)) -> forall n, P n.
intros.
assert (forall n, (forall k, k<=n -> P k)).
apply (nat_ind (fun n=>forall k, k<=n -> P k)).
intros.
apply le_n_O_eq in H1.
rewrite <- H1.
exact H.
intros.
apply le_le_S_eq in H2.
destruct H2.
apply H1.
auto with arith.
rewrite H2.
apply H0.
exact H1.
apply H1 with n.
auto with arith.
Qed.
