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

Require Export Complex.
Require Import Cmet.
Require Import Cnorm.
Require Import Rpser_def.
Require Import Max.
Require Import Csequence.
Require Import Csequence_facts.
Require Import Cprop_base.
Require Import Tools.

Open Scope C_scope.

(** * Definitions *)

(** General term of a Power Serie and its absolute value *)
Definition gt_Pser (An : nat -> C) (z : C) := fun (n:nat) => (An n) * (z ^ n).

Definition gt_norm_Pser (An : nat -> C) (z : C) := fun (n:nat) => Cnorm (An n * z ^ n).

Definition An_deriv (An:nat -> C) := fun n => INC (S n) * An (S n).

Definition gt_deriv_Pser (An : nat -> C) (z : C) := gt_Pser (An_deriv An) z.

Definition infinite_sum (s : nat -> C) (l : C) := forall eps : R,
        eps > 0 -> exists N : nat, forall n : nat, (n >= N)%nat ->
        dist C_met (sum_f_C0 s n) l < eps.
     
Definition Pser (An : nat -> C) (x l : C) :=
 infinite_sum (fun n : nat => (An n * x ^ n)) l.

Definition Pser_norm (An : nat -> C) (x : C) (l : R) := 
    Pser (fun n : nat => Cnorm (An n)) (Cnorm x) l.

(** Lower bound on the cv radius *)

Definition Cv_radius_weak (An : nat -> C) (r:R) := has_ub (gt_norm_Pser An (IRC r)).

(** Cv radius definition *)

Definition finite_cv_radius (An : nat -> C) (r:R) := 
    (forall r', 0 <= r' < r -> Cv_radius_weak An r') /\
    (forall r', r < r' -> ~ (Cv_radius_weak An r')).

Definition infinite_cv_radius (An : nat -> C) := forall (r : R), Cv_radius_weak An r.

(** * Some lemmas manipulating the definitions *)

Lemma Cv_radius_weak_0 An : Cv_radius_weak An 0.
Proof.
intro An ; exists (Cnorm (An O)) ; intros x [n Hn] ; rewrite Hn ;
 unfold gt_norm_Pser ; destruct n.
  rewrite Cpow_0 ; right ; apply Cnorm_eq_compat ; intuition.
  rewrite IRC_pow_compat, pow_i, Cmult_0_r, Cnorm_C0 ; [apply Cnorm_pos | intuition].
Qed.

Lemma finite_cv_radius_pos An r : finite_cv_radius An r -> 0 <= r.

Proof.
intros An r [_ Hf].
 destruct(Rle_lt_dec 0 r).
  trivial.
destruct (Hf 0).
trivial.
apply Cv_radius_weak_0.
Qed.

Lemma Cv_radius_weak_Cnorm_compat_rev : forall (An : nat -> C) (r : R), 
       Cv_radius_weak (fun n => Cnorm (An n)) r -> Cv_radius_weak An r.
Proof.
intros An r [M HM] ; exists M.
 intros x [n Hn] ; rewrite Hn.
 unfold gt_norm_Pser ; rewrite Cnorm_Cmult, <- Cnorm_invol, <- Cnorm_Cmult ;
 apply HM ; exists n ; reflexivity.
Qed.

Lemma Cv_radius_weak_Cnorm_compat_rev2 : forall (An : nat -> C) (r : R), 
       Rpser_def.Cv_radius_weak (fun n => Cnorm (An n)) r -> Cv_radius_weak An r.
Proof.
intros An r [M HM] ; apply Cv_radius_weak_Cnorm_compat_rev ;
 exists M ; intros x [n Hn] ; rewrite Hn ; unfold gt_norm_Pser.
 rewrite Cnorm_Cmult, IRC_pow_compat ; do 2 rewrite Cnorm_IRC_Rabs ;
 rewrite <- Rabs_mult  ; apply HM ; exists n ; reflexivity.
Qed.  

Lemma Cv_radius_weak_Cnorm_compat : forall (An : nat -> C) (r : R), 
       Cv_radius_weak An r -> Cv_radius_weak (fun n => Cnorm (An n)) r.
Proof.
intros An r Rho.
elim Rho ; intros m Hm ; exists m ; unfold gt_norm_Pser, gt_abs_Pser ; intros a Ha ;
 unfold EUn in Ha ; elim Ha ; intros u Hu ; rewrite Hu ; rewrite Cnorm_Cmult ;
 rewrite Cnorm_invol, <- Cnorm_Cmult ; apply Hm.
 exists u ; unfold gt_norm_Pser ; rewrite IRC_pow_compat ; reflexivity.
Qed.

Lemma Cv_radius_weak_Cnorm_compat2 : forall (An : nat -> C) (r : R), 
       Cv_radius_weak An r -> Rpser_def.Cv_radius_weak (fun n => Cnorm (An n)) r.
Proof.
intros An r Rho.
elim Rho ; intros m Hm ; exists m ; unfold gt_norm_Pser, gt_abs_Pser ; intros a Ha ;
 unfold EUn in Ha ; elim Ha ; intros u Hu ; rewrite Hu ; rewrite Rabs_mult ;
 do 2 rewrite <- Cnorm_IRC_Rabs ; rewrite Cnorm_invol, <- Cnorm_Cmult ; apply Hm.
 exists u ; unfold gt_norm_Pser ; rewrite IRC_pow_compat ; reflexivity.
Qed.

Lemma Cv_radius_weak_le_compat : forall (An : nat -> C) (r r' : R),
       Rabs r' <= Rabs r -> Cv_radius_weak An r -> Cv_radius_weak An r'.
Proof.
intros An r r' r'_bd Rho.
 case (Req_or_neq r') ; intro r_eq.
  rewrite r_eq ; exists (Cnorm (An 0%nat)) ; intros x Hx ; destruct Hx as (u, Hu) ;
  rewrite Hu ; unfold gt_norm_Pser ; clear ; induction u.
  apply Req_le ; apply Cnorm_eq_compat ; field.
  rewrite C0_pow ; [| intuition] ; rewrite Cmult_0_r ;
  rewrite Cnorm_C0 ; apply Cnorm_pos.
  assert (r_pos : 0 < Rabs r).
   apply Rlt_le_trans with (Rabs r') ; [apply Rabs_pos_lt |] ; assumption.
  assert (r_neq : r <> 0%R).
   case (Req_or_neq r) ; intro s ; [| assumption] ;
  apply False_ind ; rewrite s in r_pos ; rewrite Rabs_R0 in r_pos ; fourier.
  destruct Rho as (C, HC) ; exists C ; intros x Hx ; destruct Hx as (u,Hu) ; rewrite Hu ;
  unfold gt_norm_Pser.
  replace (IRC r' ^ u) with ((IRC r' ^ u * /IRC r ^ u) * (IRC r ^ u)).
  repeat (rewrite Cnorm_Cmult) ; rewrite Rmult_comm ; rewrite <- Cnorm_Cmult at 1 ;
  rewrite Rmult_assoc ; rewrite <- Cnorm_Cmult.
  apply Rle_trans with (1 * Cnorm (IRC r ^ u * An u))%R.
  apply Rmult_le_compat_r ; [apply Cnorm_pos |]. 
  rewrite Cpow_inv. rewrite <- Cpow_mul_distr_l.
  rewrite Cnorm_pow.
  replace 1%R with (1 ^ u)%R.
  apply pow_le_compat. apply Cnorm_pos.
  rewrite Cnorm_Cmult ; replace 1 with (Cnorm (IRC r) * / Cnorm (IRC r))%R.
  rewrite Cnorm_inv ; repeat rewrite Cnorm_IRC_Rabs.
  apply Rmult_le_compat_r.
  left ; apply Rinv_0_lt_compat ; apply Rabs_pos_lt ; assumption.
  assumption.
  apply IRC_neq_0_compat ; assumption.
  field ; rewrite Cnorm_IRC_Rabs ; apply Rgt_not_eq ; assumption.
  apply pow1.
  apply IRC_neq_0_compat ; assumption.
  rewrite Rmult_1_l ; apply HC.
  exists u ; unfold gt_norm_Pser ; rewrite Cmult_comm ; reflexivity.
  field.
  rewrite IRC_pow_compat ; apply IRC_neq_0_compat ;
  apply pow_nonzero ; assumption.
Qed.

Lemma finite_cv_radius_weakening : forall An r, finite_cv_radius An r ->
      forall x, Rabs x < r -> Cv_radius_weak An x.
Proof.
intros An r [H_sup _] x Hx.
 apply Cv_radius_weak_le_compat with (Rabs x).
  rewrite Rabs_Rabsolu ; right ; reflexivity.
  apply H_sup ; split ; [apply Rabs_pos | assumption].
Qed.

Lemma Cv_radius_weak_padding_pos_compat : forall (An : nat -> C) (r : R),
     Cv_radius_weak An r -> forall N, Cv_radius_weak (fun n => An (n + N)%nat) r.
Proof.
intros An r Rho N.
 destruct (Req_dec r 0) as [r_eq | r_neq].
  rewrite r_eq ; exists (Cnorm (An N)).
  intros u Hu ; destruct Hu as [n Hn] ; rewrite Hn ; unfold gt_norm_Pser ; destruct n.
  simpl ; rewrite Cmult_1_r ; right ; reflexivity.
  rewrite Cnorm_Cmult, Cnorm_pow, Cnorm_IRC_Rabs, RPow_abs, pow_i,
  Rabs_R0, Rmult_0_r ; [apply Cnorm_pos | intuition].
 destruct Rho as [M HM].
 exists (M * (/ Rabs r) ^ N)%R.
 intros u Hu ; destruct Hu as [n Hn] ; rewrite Hn.
 unfold gt_norm_Pser ; simpl.
 rewrite Cnorm_Cmult ; apply Rle_trans with (Cnorm (An (n + N)%nat) * Cnorm (r ^ n) *
 (Rabs r ^ N) * ((/Rabs r) ^ N))%R.
 right ; repeat rewrite Rmult_assoc ; repeat apply Rmult_eq_compat_l.
 rewrite <- Rpow_mult_distr, Rinv_r, pow1, Rmult_1_r ; [reflexivity |
 apply Rabs_no_R0 ; assumption].
 apply Rmult_le_compat_r.
 apply pow_le ; left ; apply Rinv_0_lt_compat ; apply Rabs_pos_lt ; assumption.
 rewrite <- Cnorm_IRC_Rabs, Rmult_assoc, <- Cnorm_pow, <- Cnorm_Cmult.
 apply HM.
 exists (n + N)%nat ; unfold gt_norm_Pser.
 repeat rewrite Cnorm_Cmult ; apply IRC_eq_compat.
 apply Rmult_eq_compat_l ; rewrite <- Cnorm_Cmult ; apply Cnorm_eq_compat.
 symmetry ; apply Cpow_add.
Qed.

Lemma Cv_radius_weak_padding_neg_compat : forall (An : nat -> C) (r : R) (N : nat),
     Cv_radius_weak (fun n => An (n + N)%nat) r -> Cv_radius_weak An r.
Proof.
intros An r N Rho.
 destruct Rho as [M HM].
 destruct (Cseq_partial_bound (fun n => (An n) * r ^ n) N) as [M' HM'].
 destruct (Req_dec r 0) as [r_eq | r_neq].
 exists (Cnorm (An 0%nat)) ; intros u Hu ; destruct Hu as [n Hn] ; rewrite Hn.
  unfold gt_norm_Pser ; destruct n.
   simpl ; rewrite Cmult_1_r ; right ; reflexivity.
   rewrite Cnorm_Cmult, Cnorm_pow, Cnorm_IRC_Rabs, r_eq, Rabs_R0, pow_i,
   Rmult_0_r ; [apply Cnorm_pos | intuition].
 exists (Rmax (M * Cnorm (r ^ N)) M') ; intros u Hu ; destruct Hu as [n Hn] ; rewrite Hn.
 destruct (le_lt_dec n N) as [n_lb | n_ub].
 apply Rle_trans with M' ; [apply HM' | apply RmaxLess2] ; assumption.
 apply Rle_trans with (M * Cnorm (r ^ N))%R ; [| apply RmaxLess1] ; unfold gt_norm_Pser.
 apply Rle_trans with (Cnorm (An n * r ^ n) * (/ Cnorm (r ^ N)) * Cnorm (r ^ N))%R.
 right ; field ; apply Cnorm_no_R0.
 apply Cpow_neq_compat ; apply IRC_neq_compat ; assumption.
  apply Rmult_le_compat_r ; [apply Cnorm_pos |].
  apply HM ; exists (n - N)%nat.
  unfold gt_norm_Pser.
  rewrite Cnorm_pow, Rinv_pow, <- Cnorm_inv, <- Cnorm_pow, <- Cnorm_Cmult,
  <- Cpow_inv.
  assert (Hrew : (n = n - N + N)%nat).
   intuition.
   repeat rewrite Cnorm_Cmult ; rewrite Hrew at 1 ; rewrite Rmult_assoc ;
   apply Rmult_eq_compat_l ; rewrite <- Cnorm_Cmult ; apply Cnorm_eq_compat.
   rewrite Hrew at 1 ; rewrite Cpow_add, Cmult_assoc, Cinv_r, Cmult_1_r ;
   [reflexivity | apply Cpow_neq_compat ; apply IRC_neq_compat ; assumption].
   apply IRC_neq_compat ; assumption.
   apply IRC_neq_compat ; assumption.
   apply Cnorm_no_R0 ; apply IRC_neq_compat ; assumption.
Qed.

Lemma Cv_radius_weak_plus : forall (An Bn : nat -> C) (r1 r2 : R),
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
 exists (C + C')%R.
 intros x Hx ; destruct Hx as (u, Hu) ; rewrite Hu ; unfold gt_norm_Pser.
 rewrite Cmult_add_distr_r ; apply Rle_trans with (Cnorm (An u *  IRC (Rmin (Rabs r1)
         (Rabs r2)) ^ u) + Cnorm (Bn u * IRC (Rmin (Rabs r1) (Rabs r2)) ^ u))%R ;
 [apply Cnorm_triang |].
 apply Rle_trans with (Cnorm (An u * IRC (Rmin (Rabs r1) (Rabs r2)) ^ u) + C')%R ;
 [apply Rplus_le_compat_l ; apply HC' | apply Rplus_le_compat_r ; apply HC] ;
 exists u ; intuition.
Qed.

Lemma Cv_radius_weak_opp : forall (An : nat -> C) (r : R),
       Cv_radius_weak An r ->
       Cv_radius_weak (fun n => - An n) r.
Proof.
intros An r Rho.
 destruct Rho as (C, HC) ; exists C ; intros x Hx ; destruct Hx as (u,Hu) ; rewrite Hu ;
 unfold gt_norm_Pser ; rewrite Copp_mult_distr_l_reverse ; rewrite Cnorm_opp ;
 apply HC ; exists u ; intuition.
Qed.

Lemma Cv_radius_weak_minus : forall (An Bn : nat -> C) (r1 r2 : R),
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

Lemma Pser_add : forall (An Bn : nat -> C) (z : C) (N : nat),
       sum_f_C0 (gt_Pser (fun n => An n + Bn n) z) N = sum_f_C0 (gt_Pser An z) N + sum_f_C0 (gt_Pser Bn z) N.
Proof.
intros An Bn x N ; induction N. 
 simpl ; unfold gt_Pser ; field.
 assert (Hrew : forall a b c d e, c = d + e -> a + b + c = a + d + (b + e)).
  intros ; subst ; field.
 simpl ; rewrite IHN ; apply Hrew.
 unfold gt_Pser ; field.
Qed.

Lemma Pser_minus : forall (An Bn : nat -> C) (x : C) (N : nat),
       sum_f_C0 (gt_Pser (fun n => An n - Bn n) x) N = sum_f_C0 (gt_Pser An x) N - sum_f_C0 (gt_Pser Bn x) N.
Proof.
intros An Bn x N ; induction N. 
 simpl ; unfold gt_Pser ; field.
 assert (Hrew : forall a b c d e, c = d - e -> a - b + c = a + d - (b + e)).
  intros ; subst ; field.
 simpl ; rewrite IHN ; apply Hrew.
 unfold gt_Pser ; field.
Qed.

Lemma Pser_Cseqcv_link (An : nat -> C) (x l : C) :
       Pser An x l ->
       Cseq_cv (fun N : nat => sum_f_C0 (gt_Pser An x) N) l.
Proof.
intros An x l H ; apply H.
Qed.