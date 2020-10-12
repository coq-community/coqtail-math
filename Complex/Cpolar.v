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

Require Import Rbase.
Require Import AltSeries.
Require Import Rseries_def.
Require Import Rtrigo_facts Ratan.
Require Import Cpow_plus.
Require Export Complex.
Require Import Lra MyRIneq.

Open Scope R_scope.

Lemma sqrt_no_R0 : forall z : R, 0 < z -> sqrt z <> 0.
Proof.
intros z z_pos Hf ; destruct (Rlt_irrefl 0) ; eapply Rlt_le_trans ;
 [| right ; eapply sqrt_eq_0 ; [left |]] ; eassumption.
Qed.

Lemma Rmult_0_lt_compat : forall a, a < 0 -> 0 < a * a.
Proof.
intros a a_neg ; apply Rlt_le_trans with ((- a) * (- a)) ;
 [| right ; ring] ; apply Rmult_lt_0_compat ; lra.
Qed.

Lemma Rle_neq_Rlt : forall a b, a <= b -> a <> b -> a < b.
Proof.
intros a b a_le a_neq ; destruct (Rlt_le_dec a b) ;
 [| destruct a_neq ; apply Rle_antisym] ; assumption.
Qed.

Lemma sqr_pos_lt : forall a, a <> 0 -> 0 < a * a.
Proof.
intros a a_neq ; destruct (Rlt_le_dec a 0).
 apply Rmult_0_lt_compat ; assumption.
 apply Rmult_lt_0_compat ; apply Rle_neq_Rlt ;
  (assumption || symmetry ; assumption).
Qed.

Lemma sqr_pos : forall b, 0 <= b * b.
Proof.
intro ; rewrite <- Rmult_1_r, Rmult_assoc ; apply sqr_pos.
Qed.

(** ** Every complex number has polar coordinate *) 

Lemma exists_polar_form : forall z : C,
  { r : R & { theta : R | z = r * cos (theta) +i r * sin (theta) } }.
Proof.
intros [a b] ; destruct (total_order_T a R0) as [[a_neg | a_eq] | a_pos].
(* case a < 0*)
 assert (Hrew : (sqrt (1 + (b / a) ^ 2) = sqrt (a * a + b * b) / sqrt ((- a) * - a))%R).
  simpl ; repeat rewrite Rmult_1_r ; rewrite <- sqrt_div.
   f_equal ; field ; apply Rlt_not_eq ; assumption.
   left ; apply Rplus_lt_le_0_compat ; [apply sqr_pos_lt, Rlt_not_eq ; assumption |
    apply sqr_pos].
   apply sqr_pos_lt, Rgt_not_eq ; lra.
 exists (- Cnorm (a +i b))%R ; exists (Ratan.atan (Cim (a +i b) / Cre (a +i b))) ;
 CusingR_simpl.
 rewrite Ratan.cos_atan ; unfold Cnorm, Cnorm_sqr ;
  rewrite Hrew ; simpl ; rewrite sqrt_square.
  field ; split ; [apply Rlt_not_eq | apply sqrt_no_R0].
   assumption.
   apply Rplus_lt_le_0_compat ; [apply sqr_pos_lt, Rlt_not_eq ; assumption |
    apply sqr_pos].
   lra.
 rewrite Ratan.sin_atan ; unfold Cnorm, Cnorm_sqr ;
  rewrite Hrew ; simpl ; rewrite sqrt_square.
  field ; split ; [apply Rlt_not_eq | apply sqrt_no_R0].
   assumption.
   apply Rplus_lt_le_0_compat ; [apply sqr_pos_lt, Rlt_not_eq ; assumption |
    apply sqr_pos].
   lra.
(* case a = 0 *)
 exists b ; exists (PI / 2) ; rewrite cos_PI2, sin_PI2, a_eq ; CusingR.
(* case 0 < a *)
 assert (Hrew : (sqrt (1 + (b / a) ^ 2) = sqrt (a * a + b * b) / sqrt (a * a))%R).
  simpl ; repeat rewrite Rmult_1_r ; rewrite <- sqrt_div.
   f_equal ; field ; apply Rgt_not_eq ; assumption.
   left ; apply Rplus_lt_le_0_compat ; [apply sqr_pos_lt, Rgt_not_eq ; assumption |
    apply sqr_pos].
   apply sqr_pos_lt, Rgt_not_eq ; lra.
 exists (Cnorm (a +i b))%R ; exists (Ratan.atan (Cim (a +i b) / Cre (a +i b))) ;
 CusingR_simpl.
 rewrite Ratan.cos_atan ; unfold Cnorm, Cnorm_sqr ;
  rewrite Hrew ; simpl ; rewrite sqrt_square.
  field ; split ; [apply Rgt_not_eq | apply sqrt_no_R0].
   assumption.
   apply Rplus_lt_le_0_compat ; [apply sqr_pos_lt, Rgt_not_eq ; assumption |
    apply sqr_pos].
   lra.
 rewrite Ratan.sin_atan ; unfold Cnorm, Cnorm_sqr ;
  rewrite Hrew ; simpl ; rewrite sqrt_square.
  field ; split ; [apply Rgt_not_eq | apply sqrt_no_R0].
   assumption.
   apply Rplus_lt_le_0_compat ; [apply sqr_pos_lt, Rgt_not_eq ; assumption |
    apply sqr_pos].
   lra.
Qed.

Lemma x_modulo_2PI : forall x, { k | 0 < IZR (k) * (2 * PI) + x <= 2 * PI }.
Proof.
intros x ; pose (k := - x / (2 * PI)) ; exists (up k) ;
 destruct (archimed k) as [k_lb k_ub].
 split.
  rewrite Rplus_comm ; apply Rminus_lt_compat_l_rev, Rmult_Rinv_lt_compat_l_rev.
   apply Rmult_lt_0_compat ; [lra | apply PI_RGT_0].
   rewrite Rminus_0_l ; apply k_lb.
  transitivity ((IZR (up k) - k) * (2 * PI)).
   right ; unfold k ; field ; apply Rgt_not_eq, PI_RGT_0.
   transitivity (1 * (2 * PI)) ; [| right ; ring] ; apply Rmult_le_compat_r.
    left ; apply Rmult_lt_0_compat ; [lra | apply PI_RGT_0].
    assumption.
Qed.

Lemma exists_principal_polar_form : forall z : C, { r : R & { theta : R |
  0 <= r /\ 0 < theta <= 2 * PI /\ r * cos (theta) +i r * sin (theta) = z } }%R.
Proof.
intro z ; destruct (exists_polar_form z) as [r [theta Hr]] ;
 destruct (Rlt_le_dec r 0) as [r_neg | r_pos].
 exists (- r) ; destruct (x_modulo_2PI (theta + PI)) as [k Hk] ;
  exists (theta + PI + 2 * IZR k * PI) ; split ; [| split].
   lra.
   replace (theta + PI + 2 * IZR k * PI) with (IZR k * (2 * PI) + (theta + PI))
    by ring ; assumption.
   subst ; CusingR.
   rewrite <- cos2PI_period, neg_cos ; ring.
   rewrite <- sin2PI_period, neg_sin ; ring.
 exists r ; destruct (x_modulo_2PI theta) as [k Hk] ;
  exists (theta + 2 * IZR k * PI) ; split ; [| split].
   assumption.
   replace (theta + 2 * IZR k * PI) with (IZR k * (2 * PI) + theta)
    by ring ; assumption.
   subst ; CusingR ; [rewrite <- cos2PI_period | rewrite <- sin2PI_period] ; ring.
Qed.
