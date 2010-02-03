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


Require Import Rtrigo.
Require Import AltSeries.
Require Import Rseries.
Require Import Ratan.
Require Import Cpow_plus.
Require Export Complex.

Open Scope R_scope.

(** ** Every complex number has polar coordinate *) 

(* TODO on fait tout le temps la meme chose *)

Lemma polar1 : forall z : C, Cre z <> 0%R -> { r : R & { theta : R | (r * cos (theta) +i r * sin (theta)) = z}}%R.
Proof.
intros. destruct z as (a,b).
destruct (total_order_T a 0%R) as [[H1|H1]|H1].
(* case a < 0*)
exists (-Cnorm (a +i b))%R.
exists (arctan(Cim (a +i b) / Cre (a +i b))).
simpl. CusingR_simpl.
(* Real*) 
rewrite arctancos. unfold Cnorm.
unfold Cmodcarre. replace (1 + (b/a) ^ 2)%R with ((a^2 + b^2) /a^2)%R. simpl.
Focus 2. field. assumption.
rewrite Ropp_mult_distr_l_reverse. unfold Rdiv. rewrite Rmult_1_l.
repeat rewrite Rmult_1_r.
generalize sqrt_div. intros H2. unfold Rdiv in *. rewrite <- H2.
simpl. field_simplify. unfold Rdiv. rewrite Rinv_1. repeat rewrite Rmult_1_r.
rewrite Rinv_mult_distr. rewrite <- Rmult_assoc. rewrite Rinv_r.
rewrite Rinv_involutive. rewrite Rmult_1_l. replace (sqrt (a * a))%R with (-a)%R.
auto with real. replace (a*a)%R with (-a * -a)%R by ring.
rewrite sqrt_square. reflexivity. fourier.
intro H10. apply Rmult_integral in H10. destruct H10 as [H10|H10] ; rewrite H10 in * ; intuition.
intro H10. apply HC0_norm_R0 with (a +i b) in H10. rewrite <- Ceq in H10.
simpl in H10 ; destruct H10 as [H10 H11]. rewrite H10 in H1. fourier.
intro H10. apply HC0_norm_R0 with (a +i b) in H10. rewrite <- Ceq in H10.
simpl in H10 ; destruct H10 as [H10 H11]. rewrite H10 in H1. fourier.
apply Rinv_neq_0_compat. intro H10. apply Rmult_integral in H10. intuition.
apply Cmodcarre_pos. apply Rlt_mult_inv_pos.
replace 0%R with (0 + 0)%R by auto with real. apply Rplus_lt_le_compat.
replace (a*a)%R with (-a * -a)%R by ring. apply Rmult_lt_0_compat ; fourier.
replace (b*b)%R with (Rsqr b)%R by (unfold Rsqr ; ring).
auto with real.  replace (a*a)%R with (-a * -a)%R by ring. apply Rmult_lt_0_compat ; fourier.
(*Imaginary*)
rewrite arctansin. unfold Cnorm. unfold Cmodcarre.
replace (1 + (b/a) ^ 2)%R with ((a^2 + b^2) /a^2)%R. simpl.
repeat rewrite Rmult_1_r. rewrite sqrt_div. 
unfold Rdiv. rewrite Rinv_mult_distr. rewrite Rinv_involutive.
rewrite Ropp_mult_distr_l_reverse. field_simplify.
rewrite Ropp_mult_distr_l_reverse. replace (sqrt(a * a))%R with (-a)%R.
field. intro H10 ; rewrite H10 in H1 ; fourier.
replace (a * a)%R with (-a * -a)%R by ring.
rewrite sqrt_square. reflexivity. intuition.
split. intro H10. apply sqrt_eq_0 in H10. 
apply HC0_norm_R0 with (a +i b) in H10. rewrite <- Ceq in H10.
simpl in H10 ; destruct H10 as [H10 H11]. rewrite H10 in H1. fourier.
apply Cmodcarre_pos. intro H10. rewrite H10 in H1. fourier.
intro H10. apply sqrt_eq_0 in H10. apply Rmult_integral in H10.
destruct H10 as [H10|H10] ; rewrite H10 in H1 ; fourier.
replace (a*a)%R with (Rsqr a)%R by (unfold Rsqr ; ring). auto with real.
intro H10. apply sqrt_eq_0 in H10. 
apply HC0_norm_R0 with (a +i b) in H10. rewrite <- Ceq in H10.
simpl in H10 ; destruct H10 as [H10 H11]. rewrite H10 in H1. fourier.
apply Cmodcarre_pos. apply Rinv_neq_0_compat.
intro H10. apply sqrt_eq_0 in H10. apply Rmult_integral in H10.
destruct H10 as [H10|H10] ; rewrite H10 in H1 ; fourier.
replace (a*a)%R with (Rsqr a)%R by (unfold Rsqr ; ring). auto with real.
apply Cmodcarre_pos. 
replace (a * a)%R with (-a * -a)%R by ring. apply Rmult_lt_0_compat ; fourier.
field. intro H10. rewrite H10 in H1. fourier.
(* a = 0*)
exists (Cnorm (a +i b)).
destruct (total_order_T b 0%R) as [[H2|H2]|H2] ; rewrite H1.
(* b< 0 *)
exists (3*(PI/2))%R.
rewrite cos_3PI2.
rewrite sin_3PI2.
unfold Cnorm. unfold Cmodcarre.
CusingR_simpl ; simpl. ring.
ring_simplify. rewrite Rmult_0_l. rewrite Rplus_0_l.
replace (b * b)%R with (-b * -b)%R. rewrite sqrt_square. ring.
fourier. ring.
(* b = 0 *)
rewrite H2. exists 0%R.
unfold Cnorm. unfold Cmodcarre. simpl. CusingR_simpl;
rewrite Rmult_0_l ; rewrite Rplus_0_l ; rewrite sqrt_0 ; ring.
(* b> 0*)
exists (PI/2)%R.
rewrite cos_PI2.
rewrite sin_PI2.
unfold Cnorm. unfold Cmodcarre.
CusingR_simpl ; simpl. ring. 
ring_simplify. rewrite Rmult_0_l. rewrite Rplus_0_l.
rewrite sqrt_square. reflexivity. fourier.
(* a > 0 *)
exists (Cnorm (a +i b))%R.
exists (arctan(Cim (a +i b) / Cre (a +i b))).
simpl. CusingR_simpl.
(* Real*) 
rewrite arctancos. unfold Cnorm.
unfold Cmodcarre. replace (1 + (b/a) ^ 2)%R with ((a^2 + b^2) /a^2)%R. simpl.
Focus 2. field. assumption.
unfold Rdiv. rewrite Rmult_1_l.
repeat rewrite Rmult_1_r.
generalize sqrt_div. intros H2. unfold Rdiv in *. rewrite <- H2.
simpl. field_simplify. unfold Rdiv. rewrite Rinv_1. repeat rewrite Rmult_1_r.
rewrite Rinv_mult_distr. rewrite <- Rmult_assoc. rewrite Rinv_r.
rewrite Rinv_involutive. rewrite Rmult_1_l. replace (sqrt (a * a))%R with (a)%R.
reflexivity. rewrite sqrt_square. reflexivity. fourier.
intro H10. apply Rmult_integral in H10. destruct H10 as [H10|H10] ; rewrite H10 in * ; intuition.
intro H10. apply HC0_norm_R0 with (a +i b) in H10. rewrite <- Ceq in H10.
simpl in H10 ; destruct H10 as [H10 H11]. rewrite H10 in H1. fourier.
intro H10. apply HC0_norm_R0 with (a +i b) in H10. rewrite <- Ceq in H10.
simpl in H10 ; destruct H10 as [H10 H11]. rewrite H10 in H1. fourier.
apply Rinv_neq_0_compat. intro H10. apply Rmult_integral in H10. intuition.
apply Cmodcarre_pos. apply Rlt_mult_inv_pos.
replace 0%R with (0 + 0)%R by auto with real. apply Rplus_lt_le_compat. 
apply Rmult_lt_0_compat ; fourier.
replace (b*b)%R with (Rsqr b)%R by (unfold Rsqr ; ring).
auto with real. apply Rmult_lt_0_compat ; fourier.
(*Imaginary*)
rewrite arctansin. unfold Cnorm. unfold Cmodcarre.
replace (1 + (b/a) ^ 2)%R with ((a^2 + b^2) /a^2)%R. simpl.
repeat rewrite Rmult_1_r. rewrite sqrt_div. 
unfold Rdiv. rewrite Rinv_mult_distr. rewrite Rinv_involutive.
field_simplify. replace (sqrt(a * a))%R with (a)%R.
field. intro H10 ; rewrite H10 in H1 ; fourier.
rewrite sqrt_square. reflexivity. intuition.
split. intro H10. apply sqrt_eq_0 in H10. 
apply HC0_norm_R0 with (a +i b) in H10. rewrite <- Ceq in H10.
simpl in H10 ; destruct H10 as [H10 H11]. rewrite H10 in H1. fourier.
apply Cmodcarre_pos. intro H10. rewrite H10 in H1. fourier.
intro H10. apply sqrt_eq_0 in H10. apply Rmult_integral in H10.
destruct H10 as [H10|H10] ; rewrite H10 in H1 ; fourier.
replace (a*a)%R with (Rsqr a)%R by (unfold Rsqr ; ring). auto with real.
intro H10. apply sqrt_eq_0 in H10. 
apply HC0_norm_R0 with (a +i b) in H10. rewrite <- Ceq in H10.
simpl in H10 ; destruct H10 as [H10 H11]. rewrite H10 in H1. fourier.
apply Cmodcarre_pos. apply Rinv_neq_0_compat.
intro H10. apply sqrt_eq_0 in H10. apply Rmult_integral in H10.
destruct H10 as [H10|H10] ; rewrite H10 in H1 ; fourier.
replace (a*a)%R with (Rsqr a)%R by (unfold Rsqr ; ring). auto with real.
apply Cmodcarre_pos.  apply Rmult_lt_0_compat ; fourier.
field. intro H10. rewrite H10 in H1. fourier.
Qed.

Lemma polar2 : forall z : C, Cre z = 0%R -> { r : R & { theta : R | (r * cos (theta) +i r * sin (theta)) = z}}%R.
Proof.
intros z Hz.
exists (Cim z).
exists (PI/2)%R.
rewrite cos_PI2.
rewrite sin_PI2.
CusingR_simpl. rewrite Hz. ring.
ring.
Qed.

Lemma polar3 : forall z : C, { r : R & { theta : R | (r * cos (theta) +i r * sin (theta)) = z}}%R.
Proof.
intros z.
destruct (total_order_T (Cre z) 0) as [[H1|H1]|H1].
assert ((Cre z) <> 0). intro H. rewrite H in H1. fourier.
apply polar1. exact H.
apply polar2. apply H1.
assert ((Cre z) <> 0). intro H. rewrite H in H1. fourier.
apply polar1. exact H.
Qed.

Lemma exists_pi_mpi : forall x, {k | 0 < IZR (k) * 2 * PI + x <= 2 * PI}.
Proof.
intros x.
exists (up ( -x / (2 * PI))).
destruct (archimed (-x / (2 * PI))) as (H, H1).
apply (Rmult_gt_compat_r (2*PI)) in H.
apply (Rmult_le_compat_r (2*PI)) in H1.
unfold Rdiv in *. rewrite Rmult_assoc in H. rewrite Rinv_l in H.
rewrite Rmult_1_r in H. apply Rgt_minus in H.
field_simplify in H1. unfold Rdiv in H1. rewrite Rinv_1 in H1.
do 2 rewrite Rmult_1_r in H1. ring_simplify in H.
intuition; ring_simplify ; assumption.
apply PI_neq0 in H1. destruct H1.
intro H10. apply Rmult_integral in H10. destruct H10 as [H10|H10]. fourier.
apply PI_neq0 in H10. destruct H10.
left. apply Rmult_gt_0_compat. fourier. apply PI_RGT_0.
apply Rmult_gt_0_compat. fourier. apply PI_RGT_0.
Qed.

Lemma polar : forall z : C, { r : R & 
{ theta : R |
 r >= 0 /\ 0 < theta <= 2 * PI /\ (r * cos (theta) +i r * sin (theta)) = z}}%R.
Proof.
intro z.
destruct (polar3 z) as [r [theta H]].
destruct (total_order_T r 0) as [[H1|H1]|H1].
exists (-r)%R.
destruct (exists_pi_mpi (theta + PI)) as (k, H2).
exists (IZR k * 2 * PI + (theta + PI))%R.
split. intuition.
split. exact H2.
rewrite Rplus_comm.
replace (IZR k * 2 * PI) with (2 * IZR k * PI) by ring.
rewrite <- cos2PI_period. rewrite <- sin2PI_period.
rewrite neg_cos. rewrite neg_sin.
CusingR. rewrite <- Ceq in H. destruct H as (H, H0). simpl in *.
rewrite <- H. ring. 
rewrite <- Ceq in H. destruct H as (H, H0). simpl in *.
rewrite <- H0. ring.
exists 0. exists (2 * PI). intuition. generalize PI_RGT_0. intros. fourier.
rewrite <- Ceq in H ; destruct H as (H, H0) ; CusingR ; simpl in * ; 
try rewrite <- H ; try rewrite <- H0 ; rewrite H1 ; ring.
exists r.
destruct (exists_pi_mpi (theta)) as (k, H2).
exists (IZR k * 2 * PI + theta).
split. intuition. split. intuition.
rewrite Rplus_comm.
replace (IZR k * 2 * PI) with (2 * IZR k * PI) by ring.
rewrite <- cos2PI_period. rewrite <- sin2PI_period.
exact H.
Qed.
