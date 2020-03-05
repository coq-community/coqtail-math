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


Require Import Reals.
Require Import Rseries_RiemannInt.
Require Import Rseries_facts.
Require Import Rtactic.
Require Import Rsequence_facts.
Require Import Lra.

Definition triangle n := INR (n * S n) / 2.

Lemma triangle_sum n : sum_f_R0 INR n = triangle n.
Proof.
 unfold triangle.
 induction n.
  simpl; field.
  
  rewrite tech5.
  rewrite IHn.
  elim_ident.
  field.
Qed.

Lemma triangle_non_negative n : 0 <= triangle n.
Proof.
 intros.
 unfold triangle.
 INR_solve.
Qed.

Lemma triangle_positive n : 0 < triangle (S n).
Proof.
 intros.
 unfold triangle.
 INR_solve.
Qed.

Lemma sum_consecutive_triangle n : triangle (S n) + triangle n = INR (S n) * INR (S n).
Proof.
 intros.
 unfold triangle.
 elim_ident.
 field.
Qed.

Lemma difference_consecutive_triangle n : (triangle (S n) - triangle n)² = INR (S n) * INR (S n).
Proof.
 intros.
 unfold "²", triangle.
 elim_ident.
 field.
Qed.

Lemma sum_triangular_tetrahedral n : sum_f_R0 triangle n = INR (n * S n * S (S n)) / 6.
Proof.
 unfold triangle.
 induction n.
  simpl.
  field.
  
  rewrite tech5, IHn.
  elim_ident.
  field.
Qed.

Definition inv_snssn n := / INR (S n * S (S n)).

Definition inv_sn n := / INR (S n).

Lemma diff_inv_snssn n : inv_snssn n = inv_sn n - inv_sn (S n).
Proof.
 intros.
 unfold inv_sn, inv_snssn.
 elim_ident.
 field.
 INR_solve.
Qed.

Lemma sum_inv_snssn n : sum_f_R0 inv_snssn n = 1 - inv_sn (S n).
Proof.
 induction n.
  compute; field.
  
  simpl.
  rewrite IHn.
  rewrite diff_inv_snssn.
  ring.
Qed.

Lemma inv_sn_cv_0 : Rseq_cv inv_sn 0.
Proof.
 intros e epos.
 assert (upepos : (0 < up (/ e))%Z).
  apply lt_IZR.
  eapply Rlt_trans.
   2:apply (archimed (/e)).
   auto with *.
 assert (upenneg : (0 <= up (/ e))%Z) by auto with *.
 destruct (IZN _ upenneg) as (N, HN).
 exists N.
 intros n Hn.
 unfold R_dist, inv_sn.
 rewrite Rminus_0_r.
 rewrite Rabs_Rinv_pos; [ | INR_solve ].
 rewrite <- (Rinv_involutive e); auto with *.
 apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat; auto with *.
  
  eapply Rle_lt_trans with (INR n); [ | INR_solve ].
  eapply Rle_trans with (IZR (up (/ e))).
   left.
   apply (archimed (/ e)).
   
   rewrite HN.
   rewrite <- INR_IZR_INZ.
   INR_solve.
Qed.

Lemma ser_cv_inv_snssn : Rser_cv inv_snssn 1.
Proof.
 replace 1 with (1 - 0) by ring.
 eapply Rseq_cv_eq_compat.
  2:apply (Rseq_cv_minus_compat (fun _ => 1) (Rseq_shift inv_sn)).
   intro n.
   unfold Rseq_minus.
   unfold Rseq_shift.
   apply sum_inv_snssn.
   
   apply Rseq_constant_cv.
   
   apply Rseq_cv_shift_compat_reciprocal.
   apply inv_sn_cv_0.
Qed.

Lemma sum_reciprocal_triangular : Rser_cv (fun n => / triangle (S n)) 2.
Proof.
 replace 2 with (2 * 1) by (compute; field).
 apply Rseq_cv_eq_compat with (Rseq_mult (Rseq_constant 2) (sum_f_R0 inv_snssn)).
  intro n.
  unfold Rseq_mult, Rseq_inv, Rseq_constant, inv_snssn, triangle.
  rewrite scal_sum.
  apply Rseq_sum_ext; intro.
  elim_ident.
  field.
  INR_solve.
  
  apply Rseq_cv_mult_compat.
   auto with *.
   apply ser_cv_inv_snssn.
Qed.
