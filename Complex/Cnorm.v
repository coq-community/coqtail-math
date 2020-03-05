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
Require Import Cpow.

(** * Cnorm comparisons to zero *)

Lemma Cnorm_0 : forall z : C, Cnorm z = 0%R -> z = C0.
Proof.
intros z Hz ; destruct z as (a, b) ; apply (proj2 (C0_norm_R0 _)).
apply sqrt_eq_0 ; [| assumption] ;
apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
Qed.

Lemma Cnorm_pos : forall z : C, 0%R <= Cnorm z.
Proof.
destruct z as (r, r0) ; unfold Cnorm ; apply sqrt_positivity ;
apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
Qed.

Lemma Cnorm_pos_lt : forall z : C, z <> 0 -> 0 < Cnorm z.
Proof.
intros z Hz ; case (Cnorm_pos z) ; intro H.
 apply H.
 destruct Hz ; apply Cnorm_0 ; symmetry ; assumption.
Qed.

Lemma Cnorm_C0 : Cnorm C0 = 0%R.
Proof.
unfold Cnorm, Cnorm_sqr ; simpl.
replace (0 * 0 + 0 * 0)%R with 0%R by ring.
exact sqrt_0.
Qed.

Lemma Cnorm_Cre_simpl : forall (a : R), Cnorm (a, R0) = Rabs a.
Proof.
intros ; unfold Cnorm, Cnorm_sqr ; simpl.
rewrite Rmult_0_r, Rplus_0_r ; apply sqrt_Rsqr_abs.
Qed.

Lemma Cnorm_Cim_simpl : forall (a : R), Cnorm (R0, a) = Rabs a.
Proof.
intros ; unfold Cnorm, Cnorm_sqr ; simpl.
rewrite Rmult_0_l, Rplus_0_l ; apply sqrt_Rsqr_abs.
Qed.

Lemma Cnorm_comm : forall (a b : R), Cnorm (a, b) = Cnorm (b, a).
Proof.
intros ; unfold Cnorm, Cnorm_sqr.
simpl ; rewrite Rplus_comm ; reflexivity.
Qed.

Lemma Cnorm_gt_not_eq : forall z, Cnorm z > 0 -> z <> 0.
Proof.
intros z Hz Hrew ; apply (Rlt_irrefl 0) ;
 rewrite <- Cnorm_C0 at 2 ;
 rewrite Hrew in Hz ; intuition.
Qed.

Lemma Cnorm_no_R0 : forall z : C, z <> 0 -> Cnorm z <> 0%R.
Proof.
intros z Hz ; apply Rgt_not_eq ; apply Cnorm_pos_lt ; assumption.
Qed.

(** * Properties of simple operators *)

Lemma Cnorm_IRC_Rabs : forall x:R, Cnorm (IRC x) = Rabs x.
Proof.
intro x ; unfold Cnorm, Cnorm_sqr ; simpl ; rewrite Rmult_0_r ;
 rewrite Rplus_0_r ; apply sqrt_Rsqr_abs.
Qed.

Lemma Cnorm_invol : forall z, Cnorm (Cnorm z) = Cnorm z.
Proof.
intro z ; rewrite Cnorm_IRC_Rabs.
apply Rabs_right.
apply Rle_ge ; apply Cnorm_pos.
Qed.

Lemma Cnorm_C1 : Cnorm C1 = 1%R.
Proof.
replace C1 with (IRC 1) by trivial ;
 rewrite Cnorm_IRC_Rabs ; exact Rabs_R1.
Qed.

Lemma Cnorm_conj_compat : forall z, Cnorm (Cconj z) = Cnorm z.
Proof.
intros z ; unfold Cconj, Cnorm, Cnorm_sqr ; simpl ; destruct z ;
 rewrite Rmult_opp_opp ; reflexivity.
Qed.

Lemma Cnorm_opp : forall z, Cnorm (-z) = Cnorm z.
Proof.
intros z ; unfold Cnorm, Cnorm_sqr ; destruct z as (a,b).
simpl ; replace (a * a + b * b)%R with (- a * - a + - b * - b)%R by field ;
 reflexivity.
Qed.

Lemma Cnorm_minus_sym : forall z1 z2, Cnorm (z1 - z2) = Cnorm (z2 - z1).
Proof.
intros ; rewrite Cminus_antisym ; rewrite Cnorm_opp ; reflexivity.
Qed.

Lemma Cnorm_mult : forall lambda : R, forall z : C,
  Cnorm (lambda `* z) = ((Rabs lambda) * (Cnorm z))%R.
Proof.
intros lambda z ; destruct z as (r1, r2) ; unfold Cnorm ; unfold Cnorm_sqr ; simpl.
replace (lambda * r1 * (lambda * r1) + lambda * r2 * (lambda * r2))%R with
  (lambda^2 * (r1 * r1 + r2 * r2))%R by ring.
rewrite sqrt_mult ; assert (sqrt (lambda ^ 2) = Rabs lambda)%R as H0.
 rewrite <- sqrt_Rsqr_abs ; simpl ; unfold Rsqr ; rewrite Rmult_1_r ; reflexivity.
 rewrite H0 ; reflexivity.
 simpl ; rewrite Rmult_1_r ; apply sqrt_Rsqr_abs.
 simpl ; rewrite Rmult_1_r ; apply Rle_0_sqr.
 simpl ; rewrite Rmult_1_r ; apply sqrt_Rsqr_abs.
 apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
Qed.

Lemma Cnorm_Cmult : forall z1 z2, Cnorm (z1 * z2) = (Cnorm z1 * Cnorm z2)%R.
Proof.
intros z1 z2 ; destruct z1 as (a,b) ; destruct z2 as (c,d) ; unfold Cnorm ; unfold Cnorm_sqr ; simpl.
  replace ((a * c - b * d) * (a * c - b * d) + (a * d + b * c) * (a * d + b * c))%R
with ((a * a + b * b) * (c * c + d * d))%R by field.
apply sqrt_mult ; apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
Qed.

Lemma Cnorm_pow : forall z n, Cnorm (z ^ n) = ((Cnorm z) ^ n)%R.
Proof.
intros z n ; induction n.
 simpl ; apply Cnorm_C1.
 simpl ; rewrite Cnorm_Cmult, IHn ; reflexivity.
Qed.

Lemma Rabs_Cnorm : forall z, Rabs (Cnorm z) = Cnorm z.
Proof.
intro z ; apply Rabs_right ; apply Rle_ge ; apply Cnorm_pos.
Qed.

Lemma Cnorm_inv : forall z : C, z <> 0 -> Cnorm (/z) = (/(Cnorm z))%R.
Proof.
intros z Hz ; unfold Cnorm, Cnorm_sqr ; destruct z as (a,b).
simpl.
replace ((a / (a * a + b * b) * (a / (a * a + b * b)) +
  - b / (a * a + b * b) * (- b / (a * a + b * b))))%R with
    (1 / (a * a + b * b))%R.
 rewrite <- Rmult_1_l ; rewrite <- sqrt_1 at 2 ; rewrite sqrt_div.
  reflexivity.
  intuition.
 case (Req_or_neq a) ; intro Ha.
 case (Req_or_neq b) ; intro Hb.
  destruct Hz ; subst ; reflexivity.
  apply Rplus_le_lt_0_compat ; [apply Rle_0_sqr |
  apply Rlt_0_sqr ; assumption].
  apply Rplus_lt_le_0_compat ; [apply Rlt_0_sqr ;
  assumption | apply Rle_0_sqr].
 field ; case (proj1 (C0_neq_R0_neq _) Hz) ; unfold Cre ; simpl ; intro H.
  apply Rgt_not_eq ; apply Rplus_lt_le_0_compat ; [apply Rlt_0_sqr ;
  assumption | apply Rle_0_sqr].
  apply Rgt_not_eq ; apply Rplus_le_lt_0_compat ; [apply Rle_0_sqr |
  apply Rlt_0_sqr ; assumption].
Qed.

(** * Triangle Inequality *)

Lemma Cnorm_triang : forall z1 z2 : C, Cnorm (z1 + z2) <= (Cnorm z1 + Cnorm z2)%R.
destruct z1 as (r0, r1) ; destruct z2 as (r2, r3) ; simpl ; apply Rsqr_incr_0. unfold Cnorm. unfold Cnorm_sqr. simpl.
 rewrite Rsqr_plus ; repeat (rewrite Rsqr_sqrt) ; [| apply Rplus_le_le_0_compat ;
 apply Rle_0_sqr | apply Rplus_le_le_0_compat ; apply Rle_0_sqr |].
 assert (H : 0 <= (r0 * r3 - r1 * r2) * (r0 * r3 - r1 * r2)) by (apply Rle_0_sqr).
 assert (2 * r0 * r2 * r1 * r3 <= (r0 * r3) * (r0 * r3) + (r1 * r2) * (r1 * r2))%R as H1.
  ring_simplify in H ; ring_simplify ; apply Rminus_le ;
  apply Ropp_le_ge_contravar in H ; rewrite Ropp_0 in H.
  assert (H0 : (-(r0^2 * r3^2 - 2 * r0 * r3 * r1 * r2 + r1^2 * r2^2) = 2 * r0 * r2 * r1 * r3 - (r0^2 * r3^2 + r2^2 * r1^2))%R).
  ring.
 rewrite <- H0 ; intuition.
 ring_simplify ; repeat (rewrite Rplus_assoc) ; apply Rplus_le_compat_l.
 rewrite Rplus_comm ; rewrite Rplus_assoc ; apply Rplus_le_compat_l ;
 rewrite Rplus_assoc ; apply Rplus_le_compat_l ; rewrite Rplus_assoc ;
 rewrite Rplus_comm ; rewrite Rplus_assoc ; apply Rplus_le_compat_l ;
 apply Rsqr_incr_0_var.
 repeat (rewrite Rsqr_mult ; rewrite Rsqr_sqrt) ; [| apply Rplus_le_le_0_compat ;
 apply Rle_0_sqr | apply Rplus_le_le_0_compat ; apply Rle_0_sqr].
 rewrite Rsqr_plus ; ring_simplify.
 assert (Temp : (Rsqr (2 * r0 * r2) = r0^2 * r2^2 * (Rsqr 2))%R).
  compute ; ring.
 rewrite <- Temp ; clear Temp.
 assert (Temp : (Rsqr (2 * r1 * r3) = r1^2 * r3^2 * Rsqr 2)%R).
  compute ; ring.
 rewrite <- Temp ; clear Temp.
 repeat rewrite Rplus_assoc ; apply Rplus_le_compat_l ; rewrite Rplus_comm ;
 repeat rewrite <- Rplus_assoc ; apply Rplus_le_compat_r ;
 replace 8%R with  (4 * 2)%R by ring ; replace (Rsqr 2)%R with 4%R by intuition ;
 rewrite <- Rmult_plus_distr_r ; rewrite Rmult_assoc ; rewrite Rmult_assoc ;
 rewrite Rmult_assoc ; rewrite Rmult_assoc ; rewrite Rmult_comm ;
 apply Rmult_le_compat_r ; [lra |].
 ring_simplify ; ring_simplify in H1 ; exact H1.
 rewrite Rmult_assoc ; apply Rmult_le_pos ; [lra |] ; apply Rmult_le_pos ;
 apply sqrt_positivity ; apply Rplus_le_le_0_compat ; apply Rle_0_sqr. 
 apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
 apply sqrt_positivity; apply Rplus_le_le_0_compat ; apply Rle_0_sqr. 
 apply Rplus_le_le_0_compat ; apply sqrt_positivity ;
 apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
Qed.

Lemma Cnorm_triang_rev : forall z1 z2 : C, Rabs (Cnorm z1- Cnorm z2) <= (Cnorm (z1 - z2)).
Proof.
intros z1 z2.
assert (H1 : Cnorm (z1 - z2 + z2) <= (Cnorm (z1 - z2)) + Cnorm z2) by (apply Cnorm_triang).
assert (H2 : Cnorm (z2 - z1 + z1) <= (Cnorm (z2 - z1)) + Cnorm z1) by (apply Cnorm_triang).
assert (H3 : forall a b, a = a - b + b).
 CusingR_f.
unfold Rabs ; case Rcase_abs ; intro H ; ring_simplify.
 rewrite <- H3 in H2 ; apply Rminus_le ; apply Rle_minus in H2 ;
  ring_simplify in H2 ; rewrite Cnorm_minus_sym ;
   replace ( -Cnorm z1 + Cnorm z2 - Cnorm (z2 - z1))%R with
    (Cnorm z2 - Cnorm (z2 - z1) - Cnorm z1)%R by field ; apply H2.
 rewrite <- H3 in H1 ; apply Rminus_le ; apply Rle_minus in H1.
 replace (Cnorm z1 - Cnorm z2 - Cnorm (z1 - z2))%R with
    (Cnorm z1 - (Cnorm(z1 - z2) + Cnorm z2))%R by field ; apply H1.
Qed.

Lemma Cnorm_triang_rev_l :  forall z1 z2 : C, Cnorm z1- Cnorm z2 <= (Cnorm (z1 - z2)).
Proof.
intros z1 z2 ; apply Rle_trans with (Rabs (Cnorm z1 - Cnorm z2)) ;
 [apply RRle_abs |
  apply Cnorm_triang_rev].
Qed.

Lemma Cnorm_triang_rev_r :  forall z1 z2 : C, Cnorm z2 - Cnorm z1 <= (Cnorm (z1 - z2)).
Proof.
intros z1 z2 ; apply Rle_trans with (Rabs (Cnorm z2 - Cnorm z1)) ;
 [apply RRle_abs |
  rewrite Rabs_minus_sym ; apply Cnorm_triang_rev].
Qed.

(** Comparisons between Cnorm & Cre/Cim *)

Lemma Cre_le_Cnorm : forall z, Rabs (Cre z) <= Cnorm z.
Proof.
intro z ; unfold Cre, Cnorm, Cnorm_sqr ; destruct z.
assert (Hrew : forall r, (r*r = r²)%R).
 intro a ; reflexivity.
 rewrite <- sqrt_Rsqr_abs.
 apply sqrt_le_1.
  intuition.
  apply Rplus_le_le_0_compat ; rewrite Hrew ; intuition.
  apply Rle_trans with (r²+0)%R.
   intuition.
   repeat (rewrite Hrew) ; apply Rplus_le_compat_l ; intuition.
Qed.

Lemma Cim_le_Cnorm : forall z, Rabs (Cim z) <= Cnorm z.
Proof.
intro z ; unfold Cim, Cnorm, Cnorm_sqr ; destruct z.
assert (Hrew : forall r, (r*r = r²)%R).
 intro a ; reflexivity.
 rewrite <- sqrt_Rsqr_abs.
 apply sqrt_le_1.
  intuition.
  apply Rplus_le_le_0_compat ; rewrite Hrew ; intuition.
  apply Rle_trans with (0 + r0²)%R.
   intuition.
   repeat (rewrite Hrew) ; apply Rplus_le_compat_r ; intuition.
Qed.

Lemma Cnorm_le_Cre_Cim : forall z, Cnorm z <= Rabs (Cre z) + Rabs (Cim z).
Proof.
intro z ; unfold Cnorm, Cnorm_sqr ; destruct z as (a,b) ; simpl.
rewrite <- sqrt_square.
 apply sqrt_le_1.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  apply Rmult_le_pos ; apply Rplus_le_le_0_compat ; apply Rabs_pos.
  apply Rle_trans with (Rabs a * Rabs a + Rabs b * Rabs b)%R.
   repeat rewrite <- Rabs_mult.
   apply Rplus_le_compat ; apply RRle_abs.
   rewrite Rmult_plus_distr_r ; repeat rewrite Rmult_plus_distr_l.
   repeat (rewrite Rplus_assoc) ; apply Rplus_le_compat_l.
   apply Rle_trans with (0 + Rabs b * Rabs b)%R ; [intuition |].
   rewrite <- Rplus_assoc ; apply Rplus_le_compat_r ;
    apply Rplus_le_le_0_compat ; apply Rmult_le_pos ; apply Rabs_pos.
 apply Rplus_le_le_0_compat ; apply Rabs_pos.
Qed.
