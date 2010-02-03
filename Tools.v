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

Require Import Rfunctions.
Require Import Fourier.

Open Local Scope R_scope.

(** Relation entre la parité et la décomposition en 2p ou 2p+1*)
(** /!\ Utiliser plutôt le lemme n_modulo_2 que des case (even n) ! *)

Fixpoint even (n:nat) : bool := match n with
 | 0 => true
 | 1 => false
 | S (S n') => even n'
end.

Definition not_b (b:bool) : bool := if b then false else true.

Lemma not_b_invol : forall b, not_b(not_b b) = b.
Proof.
intro. case_eq b.
 intro ; simpl ; reflexivity.
 intro ; simpl ; reflexivity.
Qed.

Lemma even_alt : forall n, even (S n) = not_b (even n).
Proof.
intro.
 induction n.
  trivial.
  simpl. induction n.
   trivial.
   replace (even n) with (even (S (S n))).
   rewrite IHn.
   rewrite (not_b_invol (even (S n))).
   reflexivity.
   simpl. reflexivity.
Qed.

Lemma even_alt2 : forall n, not_b(even (S n)) = even n.
Proof.
intro.
 rewrite (even_alt n).
 rewrite (not_b_invol (even n)).
 reflexivity.
Qed.

Lemma dble_recursion : (forall n, (even n = true -> exists p, n = 2*p) /\ (even n = false -> exists p, n=2*p+1))%nat.
Proof.
intro n.
induction n.
 split.
 exists 0%nat.
 simpl ; reflexivity.
 intro Heven. simpl (even 0) in Heven.
 apply False_ind ; intuition.
 destruct IHn.
 split.
 intro Heven.
  destruct H0.
  rewrite <-(even_alt2 n).
  rewrite Heven.
  trivial.
  exists (x + 1)%nat.
  rewrite H0.
  intuition.
 intro Heven.
  destruct H.
  rewrite <-(even_alt2 n).
  rewrite Heven.
  trivial.
  exists x.
  rewrite H.
  intuition.
Qed.

Lemma even_is_dble : (forall n, even n = true -> exists p, n = 2*p)%nat.
Proof.
intro n.
 apply (dble_recursion n).
Qed.

Lemma even_plus_is_odd : (forall n, even n = false -> exists p, n = 2*p+1)%nat.
Proof.
intro n.
 apply (dble_recursion n).
Qed.

(** Positivité de 1 + x^2 *)

Lemma plus_Rsqr_gt_0 : forall x, 1 + x ^ 2 > 0.
Proof.
intro x ; replace 0 with (0+0) by intuition ;
 apply Rplus_gt_ge_compat ; [intuition |].
 replace (x^2) with (x²).
 apply Rle_ge ; apply Rle_0_sqr.
 unfold Rsqr ; field.
Qed.

(** Rpow conserve les inégalités *)

Lemma pow_lt_compat : forall x y, 0 < x -> x < y ->
  forall n, (1 <= n)%nat -> x ^ n < y ^ n.
Proof.
intros x y x_pos x_lt_y n n_lb.
 induction n.
 apply False_ind ; intuition.
 destruct n.
 simpl ; repeat (rewrite Rmult_1_r) ; assumption.
 assert (Hrew : forall a n, a ^ S (S n) = a * a ^ S n).
  intros a m ; simpl ; reflexivity.
 repeat (rewrite Hrew) ; apply Rmult_gt_0_lt_compat ; [apply pow_lt | | | apply IHn] ; intuition.
 apply Rlt_trans with x ; assumption.
Qed.

Lemma pow_le_compat : forall x y, 0 <= x -> x <= y ->
  forall n, x ^ n <= y ^ n.
Proof.
intros x y x_pos x_lt_y n.
 induction n.
 simpl ; apply Req_le ; reflexivity.
 simpl ; apply Rmult_le_compat ; [| apply pow_le | |] ; assumption.
Qed.

(** Quelques théorèmes de partitionnement des ensembles N et R *)

Lemma n_modulo_2 : forall n:nat, {p | (n = 2 * p)%nat} + {p | n = S (2 * p)}.
Proof.
intro n ; induction n.
 left ; exists 0%nat ; intuition.
 case IHn ; intro H ; destruct H as (p,Hp) ;
 [right ; exists p | left ; exists (S p)] ; intuition.
Qed.

Lemma n_modulo_3 : forall n:nat, {p | (n = 3 * p)%nat}
      + {p | (n = 3 * p + 1)%nat} + { p | (n = 3 * p + 2)%nat}. 
Proof.
intro n ; induction n.
 left ; left ; exists 0%nat ; intuition.
 case IHn ; intro Hyp.
  case Hyp ; clear Hyp ; intro Hyp ; destruct Hyp as (p, Hp).
  left ; right ; exists p ; intuition.
  right ; exists p ; intuition.
  destruct Hyp as (p,Hp) ; left ; left ; exists (p+1)%nat ; intuition.
Qed.

Lemma Neq_or_neq : forall m n:nat, {(m=n)%nat} + {(m<>n)%nat}.
Proof.
intros m n.
 case (le_lt_dec m n) ; intro s.
 case (le_lt_dec n m) ; intro s'.
 left ; intuition.
 right ; intuition.
 right ; intuition.
Qed.

(** D'un intervall {x | lb < x < ub} on peut tirer une boule *)

Lemma ub_lt_2_pos : forall x ub lb, lb < x -> x < ub -> 0 < (ub-lb)/2.
Proof.
intros x ub lb lb_lt_x x_lt_ub.
 assert (T : 0 < ub - lb).
  fourier.
 unfold Rdiv ; apply Rlt_mult_inv_pos ; intuition.
Qed.

Definition mkposreal_lb_ub (x lb ub:R) (lb_lt_x:lb<x) (x_lt_ub:x<ub) : posreal.
intros x lb ub lb_lt_x x_lt_ub.
 apply (mkposreal ((ub-lb)/2) (ub_lt_2_pos x ub lb lb_lt_x x_lt_ub)).
Defined.

(** Pour tout epsilon, il est possible de trouver un N tel que pour tout n > N, 1/(2*n+1) < eps *)

Lemma eps_gives_N : forall eps, eps > 0 -> exists N:nat, forall n, (n >= N)%nat -> Rabs ((-1)^n * 1/ (INR (2*n+1))) < eps.
  intros eps' eps'_pos.
   exists (Zabs_nat (up (1/eps'))).
   intros n n_gt_N.
 assert (eps_neq : eps' <> 0).
  apply Rgt_not_eq ; assumption.
 assert (inv_eps_pos : 1 / eps' > 0).
  unfold Rdiv ; rewrite Rmult_1_l ; apply Rinv_0_lt_compat ; assumption.
  assert (IZR_INR : (forall x, x > 0 -> IZR x = INR (Zabs_nat x))%Z).
   intros x x_pos.
    rewrite INR_IZR_INZ, inj_Zabs_nat, Zabs_eq.
    reflexivity. omega.
 assert (Sublemma : (0 < up (1 / eps'))%Z).
  apply lt_IZR. apply Rlt_trans with (r2:=(1 / eps')).
  simpl ; assumption.
  apply (proj1 (archimed (1 / eps'))).
  assert (Sublemma2 : (0 < n)%nat).
  apply INR_lt.
   apply Rge_gt_trans with (r2:=INR (Zabs_nat (up (1 / eps')))).
   assert (ge_INR : forall m n, (m >= n)%nat -> INR m >= INR n).
    intros m0 n0 m0_ge_n0.
    intuition.
   apply ge_INR ; assumption.
   apply lt_INR. simpl. apply INR_lt ; apply Rlt_le_trans with (r2:=1/eps'). 
   simpl ; assumption.
   apply Rlt_le. replace (INR (Zabs_nat (up (1 / eps')))) with (IZR (up (1 / eps'))).
   apply (proj1 (archimed (1 / eps'))).
   apply IZR_INR. apply Zlt_gt ; assumption.
 unfold Rdiv ; rewrite Rmult_assoc ; rewrite Rabs_mult ; rewrite pow_1_abs ; rewrite Rmult_1_l.
 apply Rlt_trans with (r2:=/ INR (n)).
 rewrite Rmult_1_l ; rewrite Rabs_Rinv ; [apply Rinv_lt_contravar | apply Rgt_not_eq ;
   replace 0 with (INR 0) by intuition ; apply lt_INR ; intuition].
 apply Rmult_lt_0_compat.
 intuition.
 apply Rlt_trans with (r2:=INR n).
  intuition.
 assert (Temp : forall n, Rabs (INR n) = INR n).
  intro k. rewrite Rabs_right ; intuition.
 rewrite Temp.
 apply lt_INR ; intuition.
 assert (Temp : forall n, Rabs (INR n) = INR n).
  intro k. rewrite Rabs_right ; intuition.
 rewrite Temp.
 apply lt_INR ; intuition.
 rewrite <-Rinv_involutive.
 apply Rinv_lt_contravar. apply Rmult_lt_0_compat.
 intuition. intuition.
 apply Rlt_le_trans with (r2:= INR (Zabs_nat (up (1 / eps')))).
 rewrite <-IZR_INR.
 replace (/eps') with (1/eps').
 apply (proj1 (archimed (1 / eps'))).
 unfold Rdiv ; apply Rmult_1_l ; reflexivity.
 intuition. intuition.
 assumption.
Qed.
