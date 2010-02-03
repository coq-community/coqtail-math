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

Require Export Raxioms.
Require Import RIneq.
Require Import Rfunctions.
Require Import Ranalysis_def.

Open Scope R_scope.

Implicit Type r : R.

Lemma Rabs_eq_compat : forall r1 r2, r1 = r2 -> Rabs r1 = Rabs r2.
Proof.
intros ; subst ; reflexivity.
Qed.

Lemma Req_dec : forall r1 r2, {r1 = r2} + {r1 <> r2}.
Proof.
intros r1 r2.
destruct (total_order_T r1 r2) as [[Hlt|Heq]|Hgt].
right; intro Hn; apply (Rlt_irrefl r2);
  rewrite Hn in Hlt; assumption.
left; assumption.
right; intros Hn; apply (Rlt_irrefl r2);
  rewrite Hn in Hgt; assumption.
Qed.

Lemma Req_or_neq : forall r, {r = 0} + {r <> 0}.
Proof.
intros r; exact (Req_dec r 0).
Qed.

Lemma Rplus_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 + r = r2 + r.
Proof.
intros r r1 r2 H; rewrite H; reflexivity.
Qed.

Lemma Rmult_eq_compat_r : forall r1 r2 r, r1 = r2 -> r1 * r = r2 * r.
Proof.
intros r1 r2 r r_neq.
 rewrite Rmult_comm.
 replace (r2 * r) with (r * r2) by field.
 apply Rmult_eq_compat_l ; assumption.
Qed.

Lemma Rmax_lt_lt_lt : forall x y z, Rmax x y < z <-> x < z /\ y < z.
 intros x y z. split.
  unfold Rmax. case (Rle_dec x y) ; intros Hyp Hyp2.
  split. apply Rle_lt_trans with (r2:=y) ; assumption. assumption.
  split. assumption. apply Rlt_trans with (r2:=x).
  assert (Temp : forall x y, ~ x <= y -> x > y).
   intros m n Hypmn. intuition.
  apply Temp ; clear Temp ; assumption.
  assumption.
  intros Hyp.
  unfold Rmax. case (Rle_dec x y).
  intro ; exact (proj2 Hyp).
  intro ; exact (proj1 Hyp).
Qed.

Lemma Rmax_le_le_le : forall x y z, Rmax x y <= z <-> x <= z /\ y <= z.
 intros x y z. split.
  unfold Rmax. case (Rle_dec x y) ; intros Hyp Hyp2.
  split. apply Rle_trans with (r2:=y) ; assumption. assumption.
  split. assumption. apply Rle_trans with (r2:=x).
  assert (Temp : forall x y, ~ x <= y -> x > y).
   intros m n Hypmn. intuition.
   left ; apply Temp ; clear Temp ; assumption.
  assumption.
  intros Hyp.
  unfold Rmax. case (Rle_dec x y).
  intro ; exact (proj2 Hyp).
  intro ; exact (proj1 Hyp).
Qed.

Lemma Rmin_gt_gt_gt : forall x y z, Rmin x y > z <-> x > z /\ y > z.
 intros x y z. split.
  unfold Rmin. case (Rle_dec x y) ; intros Hyp Hyp2.
  split. assumption.
  apply Rlt_le_trans with (r2:=x) ; intuition.
  split.
  apply Rlt_trans with (r2:=y). intuition.
  assert (Temp : forall x y, ~ x <= y -> x > y).
   intros m n Hypmn. intuition.
  apply Temp ; clear Temp ; assumption.
  assumption.
  intros Hyp.
  unfold Rmin. case (Rle_dec x y).
  intro ; exact (proj1 Hyp).
  intro ; exact (proj2 Hyp).
Qed.

Lemma Rmin_ge_ge_ge : forall x y z, Rmin x y >= z <-> x >= z /\ y >= z.
 intros x y z. split.
  unfold Rmin. case (Rle_dec x y) ; intros Hyp Hyp2.
  split ; [assumption | apply Rle_ge].
  apply Rle_trans with (r2:=x) ; intuition.
  split ; [apply Rle_ge | assumption].
  apply Rle_trans with (r2:=y). intuition.
  assert (Temp : forall x y, ~ x <= y -> x > y).
   intros m n Hypmn. intuition.
   left ; apply Temp ; clear Temp ; assumption.
  intros Hyp.
  unfold Rmin. case (Rle_dec x y).
  intro ; exact (proj1 Hyp).
  intro ; exact (proj2 Hyp).
Qed.

Lemma Rle_neq_lt : forall x y, x <= y /\ x <> y -> x < y.
Proof.
intros m n Hyp. unfold Rle in Hyp.
 destruct Hyp as (Hyp1,Hyp2).
 case Hyp1.
 intuition.
 intro Hfalse ; apply False_ind ; apply Hyp2 ; exact Hfalse.
Qed.

Definition middle (x:R) (y:R) : R := (x+y)/2.

Lemma middle_interval : forall lb ub x y, interval lb ub x -> interval lb ub y ->
       interval lb ub (middle x y).
Proof.
intros lb ub x y x_in_I y_in_I.
 split ; unfold middle, interval in *.
 replace lb with ((lb + lb) * /2) by field.
 unfold Rdiv ; apply Rmult_le_compat_r ; intuition.
 replace ub with ((ub + ub) * /2) by field.
 unfold Rdiv ; apply Rmult_le_compat_r ; intuition.
Qed.