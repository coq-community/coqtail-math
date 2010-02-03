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

Require Export Reals.
Require Export MyReals.
Require Import Max.
Require Import Tools.
Require Import Fourier.

Open Local Scope R_scope.


(** * Definitions *)

(** General term of a Power Serie and its absolute value *)
Definition gt_Pser (An : nat -> R) (x : R) := fun (n:nat) => (An n) * (x ^ n).

Definition gt_abs_Pser (An : nat -> R) (x : R) := fun (n:nat) => Rabs(An n * x ^ n).

Definition An_deriv (An:nat -> R) := fun n => INR (S n) * An (S n).

Definition gt_deriv_Pser (An : nat -> R) (x : R) := gt_Pser (An_deriv An) x.

Definition Pser_abs (An : nat -> R) (x l: R) := 
    Pser (fun n : nat => Rabs (An n)) (Rabs x) l.

(** Lower bound on the cv radius *)

Definition Cv_radius_weak (An : nat -> R) (r:R) := has_ub (gt_abs_Pser An r).

(** Cv radius definition *)

Definition finite_cv_radius (An : nat -> R) (r:R) := 
    is_lub (fun r0 => has_ub (gt_abs_Pser An r0) ) r.

Definition infinite_cv_radius (An : nat -> R) := forall (r : R), Cv_radius_weak An r.

(** * Some lemmas manipulating the definitions *)

Lemma Cv_radius_weak_Rabs_compat : forall (An : nat -> R) (r : R), 
       Cv_radius_weak An r -> Cv_radius_weak (fun n => Rabs (An n)) r.
Proof.
intros An r Rho.
elim Rho ; intros m Hm ; exists m ; unfold gt_abs_Pser ; intros a Ha ;
 unfold EUn in Ha ; elim Ha ; intros i Hi ; rewrite Hi ; rewrite Rabs_mult ;
 rewrite Rabs_Rabsolu ; rewrite <- Rabs_mult ; apply Hm ; exists i ; unfold gt_abs_Pser ;
 reflexivity.
Qed.

Lemma Cv_radius_weak_le_compat : forall (An : nat -> R) (r r' : R),
       Rabs r' <= Rabs r -> Cv_radius_weak An r -> Cv_radius_weak An r'.
Proof.
intros An r r' r'_bd Rho.
 case (Req_or_neq r') ; intro r_eq.
  rewrite r_eq ; exists (Rabs (An 0%nat)) ; intros x Hx ; destruct Hx as (i, Hi) ;
  rewrite Hi ; unfold gt_abs_Pser ; clear ; induction i ; [apply Req_le ;
  apply Rabs_eq_compat ; field | rewrite pow_i ; intuition ; rewrite Rmult_0_r ;
  rewrite Rabs_R0 ; apply Rabs_pos].
  assert (r_pos : 0 < Rabs r).
   apply Rlt_le_trans with (Rabs r') ; [apply Rabs_pos_lt |] ; assumption.
  assert (r_neq : r <> 0).
   case (Req_or_neq r) ; intro s ; [| assumption] ;
  apply False_ind ; rewrite s in r_pos ; rewrite Rabs_R0 in r_pos ; fourier.
  destruct Rho as (C, HC) ; exists C ; intros x Hx ; destruct Hx as (i,Hi) ; rewrite Hi ;
  unfold gt_abs_Pser.
  replace (r' ^ i) with ((r' ^ i * /r ^ i) * (r ^ i)).
  repeat (rewrite Rabs_mult) ; rewrite Rmult_comm ; rewrite <- Rabs_mult at 1 ;
  rewrite Rmult_assoc ; rewrite <- Rabs_mult.
  apply Rle_trans with (1 * Rabs (r ^ i * An i)).
  apply Rmult_le_compat_r ; [apply Rabs_pos | rewrite Rinv_pow] ;
  [|assumption].
  rewrite <- Rpow_mult_distr ; rewrite <- RPow_abs ; replace 1 with (1 ^ i) ;
  [|apply pow1] ; apply pow_le_compat ; [apply Rabs_pos | rewrite Rabs_mult].
  replace 1 with ((Rabs r) * /(Rabs r)) ; [rewrite Rabs_Rinv ; [apply Rmult_le_compat_r ;
  [apply Rlt_le ; apply Rinv_0_lt_compat |] |] | apply Rinv_r ; apply Rgt_not_eq] ;
  assumption.
  rewrite Rmult_1_l ; rewrite Rmult_comm ; apply HC ; exists i ; reflexivity.
  field ; apply pow_nonzero ; assumption.
Qed.

Lemma Cv_radius_weak_plus : forall (An Bn : nat -> R) (r1 r2 : R),
       Cv_radius_weak An r1 -> Cv_radius_weak Bn r2 ->
       Cv_radius_weak (fun n => An n + Bn n) (Rmin (Rabs r1) (Rabs r2)).
Proof.
intros An Bn r1 r2 RhoA RhoB.
assert (r''_bd1 : Rabs (Rmin (Rabs r1) (Rabs r2)) <= Rabs r1).
 unfold Rmin ; case (Rle_dec (Rabs r1) (Rabs r2)) ; intro H ;
 rewrite Rabs_Rabsolu ; intuition.
assert (r''_bd2 : Rabs (Rmin (Rabs r1) (Rabs r2)) <= Rabs r2).
 unfold Rmin ; case (Rle_dec (Rabs r1) (Rabs r2)) ; intro H ;
 rewrite Rabs_Rabsolu ; intuition.
assert (Rho'A := Cv_radius_weak_le_compat An _ _ r''_bd1 RhoA).
assert (Rho'B := Cv_radius_weak_le_compat Bn _ _ r''_bd2 RhoB).
 destruct Rho'A as (C, HC) ;
 destruct Rho'B as (C', HC') ;
 exists (C + C').
 intros x Hx ; destruct Hx as (i, Hi) ; rewrite Hi ; unfold gt_abs_Pser.
 rewrite Rmult_plus_distr_r ; apply Rle_trans with (Rabs (An i *  Rmin (Rabs r1)
         (Rabs r2) ^ i) + Rabs (Bn i * Rmin (Rabs r1) (Rabs r2) ^ i)) ; [apply Rabs_triang |].
 apply Rle_trans with (Rabs (An i * Rmin (Rabs r1) (Rabs r2) ^ i) + C') ;
 [apply Rplus_le_compat_l ; apply HC' | apply Rplus_le_compat_r ; apply HC] ;
 exists i ; intuition.
Qed.

Lemma Cv_radius_weak_opp : forall (An : nat -> R) (r : R),
       Cv_radius_weak An r ->
       Cv_radius_weak (fun n => - An n) r.
Proof.
intros An r Rho.
 destruct Rho as (C, HC) ; exists C ; intros x Hx ; destruct Hx as (i,Hi) ; rewrite Hi ;
 unfold gt_abs_Pser ; rewrite Ropp_mult_distr_l_reverse ; rewrite Rabs_Ropp ;
 apply HC ; exists i ; intuition.
Qed.

Lemma Cv_radius_weak_minus : forall (An Bn : nat -> R) (r1 r2 : R),
       Cv_radius_weak An r1 -> Cv_radius_weak Bn r2 ->
       Cv_radius_weak (fun n => An n - Bn n) (Rmin (Rabs r1) (Rabs r2)).
Proof.
intros An Bn r1 r2 RhoA RhoB.
 assert (Rho'B := Cv_radius_weak_opp Bn _ RhoB).
 unfold Rminus ; apply Cv_radius_weak_plus ; assumption.
Qed.

Lemma Rmin_ge_0 : forall x y, 0 <= x -> 0 <= y -> 0 <= Rmin x y.
Proof.
intros x y x_pos y_pos.
 unfold Rmin ; case (Rle_dec x y) ; intro h ; intuition.
Qed.

Lemma Pser_add : forall (An Bn : nat -> R) (x : R) (N : nat),
       sum_f_R0 (gt_Pser (fun n => An n + Bn n) x) N = sum_f_R0 (gt_Pser An x) N + sum_f_R0 (gt_Pser Bn x) N.
Proof.
intros An Bn x N ; induction N. 
 compute ; field.
 assert (Hrew : forall a b c d e, c = d + e -> a + b + c = a + d + (b + e)).
  intros ; repeat (rewrite Rplus_assoc) ; apply Rplus_eq_compat_l ;
  replace (d + (b + e)) with (b + (d + e)) by field ; apply Rplus_eq_compat_l ;
  assumption.
 simpl ; rewrite IHN ; apply Hrew.
 unfold gt_Pser ; field.
Qed.

Lemma Pser_minus : forall (An Bn : nat -> R) (x : R) (N : nat),
       sum_f_R0 (gt_Pser (fun n => An n - Bn n) x) N = sum_f_R0 (gt_Pser An x) N - sum_f_R0 (gt_Pser Bn x) N.
Proof.
intros An Bn x N ; induction N. 
 compute ; field.
 assert (Hrew : forall a b c d e, c = d - e -> a - b + c = a + d - (b + e)).
  intros ; unfold Rminus ; repeat (rewrite Rplus_assoc) ; apply Rplus_eq_compat_l ;
  replace (d + - (b + e)) with (- b + (d - e)) by field ; apply Rplus_eq_compat_l ;
  assumption.
 simpl ; rewrite IHN ; apply Hrew.
 unfold gt_Pser ; field.
Qed.

(** Pser and Un_cv are linked. See "tech12" for the reciprocal lemma *)

Lemma Pser_Uncv_link : forall (An : nat -> R) (x l : R),
       Pser An x l ->
       Un_cv (fun N : nat => sum_f_R0 (gt_Pser An x) N) l.
Proof.
intros An x l Hyp.
 unfold gt_Pser.
 apply Hyp.
Qed.