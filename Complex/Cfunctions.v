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
Require Export Cnorm.
Require Import Ctacfield.
Require Import Cprop_base.
Require Import Cpow.
Require Import Lia.

Open Scope C_scope.

(** * Finite sum of (nat -> C) sequences *)

Fixpoint sum_f_C0 (f : nat -> C) (n : nat) : C := 
match n with
     | 0%nat => f 0%nat
     | S n' => sum_f_C0 f n' + f n
end.

(** *** Finite sum properties *)

Lemma sum_f_C0_simpl : forall (n : nat) (f : nat -> C), 
  sum_f_C0 f (S n) = sum_f_C0 f n + f (S n).
Proof.
intros.
reflexivity.
Qed.

Lemma sum_f_C0_eq_seq : forall (n : nat) (f g : nat -> C),
  (forall m : nat, (m <= n)%nat -> f m = g m) -> 
    sum_f_C0 f n = sum_f_C0 g n.
Proof.
intros n f g H.
induction n.
 simpl. apply H. intuition.
 
 simpl. rewrite IHn. 
  rewrite H with (S n) ; intuition. 

  intros m H2. apply H. intuition. 
Qed.

Lemma sum_f_C0_reindex : forall (n : nat) (f : nat -> C),  
  (f O) + sum_f_C0 (fun k : nat => f (S k)) n  = sum_f_C0 f (S n).
Proof.
intros n f.
induction n.
 simpl. ring.

 simpl. rewrite <- Cadd_assoc. rewrite IHn. simpl. ring.
Qed.

Definition q_pow_i (q : C) (n : nat) : C := q ^ n.

Lemma sum_q_pow_i : forall (q : C) (m k : nat),
  q <> C1 ->
  sum_f_C0 (fun n : nat => q_pow_i q (m + n)) k = q^m * (C1 - q ^ S k) / (C1 - q).
Proof.
intros q m k q_neq_1.
 induction k.
 simpl ; unfold q_pow_i.
 unfold Cdiv ; rewrite Cmult_assoc.
 rewrite Cmult_1_r, Cinv_r, Cmult_1_r.
 rewrite plus_0_r ; reflexivity.
 intro Hf ; apply q_neq_1 ; intuition.
 simpl sum_f_C0 ; rewrite IHk ; clear IHk.
 unfold Cdiv, q_pow_i ; simpl.
 replace (q ^ (m + S k)) with (q ^ m * (q ^ (S k))).
 repeat rewrite Cmult_assoc ; rewrite <- Cmult_add_distr_l ;
 apply Cmult_eq_compat_l.
 replace (q ^ S k) with ((q ^ S k * (C1 - q)) * / (C1 - q)).
 simpl ; auto with complex.
 field ; intro Hf ; apply q_neq_1 ; intuition.
 rewrite Cmult_assoc, Cinv_r, Cmult_1_r.
 reflexivity.
 intro Hf ; apply q_neq_1 ; intuition.
induction k.
 replace (m + 1)%nat with (S m) by ring ; simpl. rewrite Cmult_1_r. field.
 replace (m + S (S k))%nat with (S (m + S k)) by ring ; simpl ;
 rewrite <- IHk ; simpl ; field.
Qed.

(** Compatibility with operations on C *)

Lemma sum_f_C0_0 : forall n : nat, sum_f_C0 (fun n: nat => 0) n = 0.
Proof.
induction n. reflexivity.
simpl. rewrite IHn. auto with complex.
Qed.

Lemma sum_f_C0_const : forall (n : nat) (a : C), 
a * INC (S n)  = sum_f_C0 (fun _ => a) (n).
Proof.
intros n a.
induction n.
simpl. eauto with *.
rewrite S_INC. rewrite sum_f_C0_simpl. rewrite <- IHn. field.
Qed.

Lemma sum_f_C0_const_1 : forall (n : nat) (a : C), 
a   = sum_f_C0 (fun _ => a/INC( S n )) (n).
Proof.
unfold Cdiv.
intros.
rewrite <- sum_f_C0_const.
field. apply not_0_INC. intuition lia.
Qed.

Lemma sum_f_C0_mult : forall (z : C) (f : nat -> C) (N : nat),   
     z * (sum_f_C0 (fun n => f n) N) = sum_f_C0 (fun n => z* (f n)) N .
Proof.
intros z f0 n.
induction n.
 reflexivity.
simpl ; rewrite <- IHn ; ring.
Qed.

Lemma sum_f_C0_div : forall (z : C) (f : nat -> C) (N : nat),   
     z <> 0 -> (sum_f_C0 (fun n => f n) N) / z = sum_f_C0 (fun n => (f n)  / z) N .
Proof.
intros z f0 n H.
induction n.
 reflexivity.
simpl ; rewrite <- IHn ; field. exact H.
Qed.

(** Compatibility with the operators *)

Lemma sum_f_C0_add_compat : forall (f g : nat -> C) (N : nat),
     sum_f_C0 (fun n => f n + g n) N = sum_f_C0 f N + sum_f_C0 g N.
Proof.
induction N.
 reflexivity.
 simpl ; rewrite IHN ; ring.
Qed.

Lemma sum_f_C0_opp_compat : forall (f : nat -> C) (N : nat),
     sum_f_C0 (fun n => - f n) N = - sum_f_C0 f N.
Proof.
induction N.
 reflexivity.
 simpl ; rewrite IHN ; ring.
Qed.

Lemma sum_f_C0_minus_compat : forall (f g : nat -> C) (N : nat),
     sum_f_C0 (fun n => f n - g n) N = sum_f_C0 f N - sum_f_C0 g N.
Proof.
induction N.
 reflexivity.
 simpl ; rewrite IHN ; ring.
Qed.

(** Compatibility with the projectors *)

Lemma sum_f_C0_Cre_compat : forall (f : nat -> C) (N : nat),
     sum_f_R0 (fun n => Cre (f n)) N = Cre (sum_f_C0 f N).
Proof.
induction N.
 reflexivity.
 simpl ; rewrite IHN ; rewrite Cre_add_compat ; reflexivity.
Qed.

Lemma sum_f_C0_Cim_compat : forall (f : nat -> C) (N : nat),
     sum_f_R0 (fun n => Cim (f n)) N = Cim (sum_f_C0 f N).
Proof.
induction N.
 reflexivity.
 simpl ; rewrite IHN ; rewrite Cim_add_compat ; reflexivity.
Qed.

Lemma sum_f_C0_Cnorm_compat : forall (f : nat -> C) (N : nat),
      Cnorm (sum_f_C0 f N) <= sum_f_R0 (fun n => Cnorm (f n)) N.
Proof.
induction N.
right. reflexivity.
simpl. eapply Rle_trans. apply Cnorm_triang.
apply Rplus_le_compat. apply IHN. right. reflexivity.
Qed.

(** Simple upper bound on the sum *)

Lemma sum_f_C0_triang : forall (f : nat -> C) (N : nat),
     Cnorm (sum_f_C0 f N) <= sum_f_R0 (fun n => Cnorm (f n)) N.
Proof.
induction N ; simpl.
 intuition.
 apply Rle_trans with (Cnorm (sum_f_C0 f N) + Cnorm (f (S N)))%R.
 apply Cnorm_triang.
 apply Rplus_le_compat_r ; assumption.
Qed.
