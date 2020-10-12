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

(** Properties of real sequences. *)
Require Import Max.
Require Export Rseries_facts.
Require Export Rsequence_facts.
Require Import Lia Lra.
Require Import Complex.
Require Import Csequence_facts.
Require Import Cseries.
Open Scope C_scope.
Open Scope Cseq_scope.

Lemma Cser_cv_re_compat : forall Un l, Cser_cv Un l -> 
  Rser_cv (fun n : nat => Cre (Un n)) (Cre l).
Proof.
intros Un l HC.
apply Rseq_cv_eq_compat with (fun n => Cre (sum_f_C0 Un n)).
 intro; rewrite sum_f_C0_Cre_compat; trivial.
 apply Cseq_cv_re_compat.
 apply HC.
Qed.

Lemma Cser_cv_im_compat : forall Un l, Cser_cv Un l -> 
  Rser_cv (fun n : nat => Cim (Un n)) (Cim l).
Proof.
intros Un l HC.
apply Rseq_cv_eq_compat with (fun n => Cim (sum_f_C0 Un n)).
 intro; rewrite sum_f_C0_Cim_compat; trivial.
 apply Cseq_cv_im_compat.
 apply HC.
Qed.

Lemma Cser_cv_re_im_compat : forall Un l,
  Rser_cv (fun n => Cre (Un n)) (Cre l) ->
  Rser_cv (fun n => Cim (Un n)) (Cim l) ->
  Cser_cv Un l.
Proof.
intros Un l HCre HCim.
apply Cseq_cv_re_im_compat.
 apply Rseq_cv_eq_compat with (sum_f_R0 (fun n => Cre (Un n))).
  intro; rewrite <- sum_f_C0_Cre_compat; trivial.
  apply HCre.
 apply Rseq_cv_eq_compat with (sum_f_R0 (fun n => Cim (Un n))).
  intro; rewrite <- sum_f_C0_Cim_compat; trivial.
  apply HCim.
Qed.

Lemma Ccauchy_product : forall An Bn la lb lna,
 Cser_cv An la -> 
 Cser_cv Bn lb -> 
 Cser_abs_cv An lna -> 
 Cser_cv ((fun k:nat => sum_f_C0 (fun p:nat => An p * Bn (k - p)%nat) k)%C)
   (la * lb)%C.
Proof.
intros An Bn la lb lna HA HB HNA.
assert (HNAre : {lnare | Rser_abs_cv (fun n => Cre (An n)) lnare}).
 apply Rser_pos_maj_cv with (fun n => Cnorm (An n)).
  intro; apply Rabs_pos.
  intro; apply Cnorm_pos.
  intro; unfold Rseq_abs; apply Cre_le_Cnorm.
  exists lna; apply HNA.
destruct HNAre as [lnare HNAre].

assert (HNAim : {lnaim | Rser_abs_cv (fun n => Cim (An n)) lnaim}).
 apply Rser_pos_maj_cv with (fun n => Cnorm (An n)).
  intro; apply Rabs_pos.
  intro; apply Cnorm_pos.
  intro; unfold Rseq_abs; apply Cim_le_Cnorm.
  exists lna; apply HNA.
destruct HNAim as [lnaim HNAim].

apply Cser_cv_re_im_compat.
 rewrite Cre_mul.
 apply Rser_cv_ext with (fun k =>
   sum_f_R0 (fun p => ((Cre (An p) * Cre (Bn (k - p)%nat)))%R) k -
   sum_f_R0 (fun p => ((Cim (An p) * Cim (Bn (k - p)%nat)))%R) k )%R.
  repeat (intro; rewrite <- sum_f_C0_Cre_compat; rewrite <- minus_sum; apply Rseq_sum_ext).
  intro; rewrite <- Cre_mul; trivial.
  
  apply Rser_cv_minus_compat.
   eapply (Rser_cv_prod_compat (fun n => Cre (An n)) (fun n => Cre (Bn n)));
     try (apply Cser_cv_re_compat; auto).
   apply HNAre.
   
   eapply (Rser_cv_prod_compat (fun n => Cim (An n)) (fun n => Cim (Bn n)));
     try (apply Cser_cv_im_compat; auto).
   apply HNAim.
 
 rewrite Cim_mul.
 apply Rser_cv_ext with (fun k =>
   sum_f_R0 (fun p => ((Cre (An p) * Cim (Bn (k - p)%nat)))%R) k +
   sum_f_R0 (fun p => ((Cim (An p) * Cre (Bn (k - p)%nat)))%R) k )%R.
  intro; rewrite <- sum_f_C0_Cim_compat ; rewrite <- plus_sum ; apply Rseq_sum_ext.
  intro; rewrite Cim_mul; ring.
  
  apply Rser_cv_plus_compat.
   eapply (Rser_cv_prod_compat (fun n => Cre (An n)) (fun n => Cim (Bn n))).
    apply Cser_cv_re_compat; auto.
    apply Cser_cv_im_compat; auto.
    apply HNAre.
   
   rewrite Rmult_comm.
   eapply (Rser_cv_prod_compat (fun n => Cim (An n)) (fun n => Cre (Bn n))).
    apply Cser_cv_im_compat; auto.
    apply Cser_cv_re_compat; auto.
    apply HNAim.
Qed.

Lemma Cser_cv_unique : forall Un l1 l2, Cser_cv Un l1 -> Cser_cv Un l2 -> l1 = l2.
Proof.
intros Un l1 l2 H H'.
apply Cseq_cv_unique with (sum_f_C0 Un); auto.
Qed.

Lemma Csum_eq_compat_weak : forall Un Vn n,
  (forall j, Un j = Vn j) -> sum_f_C0 Un n = sum_f_C0 Vn n.
Proof.
intros Un Vn n H.
induction n.
 apply H.
 simpl; rewrite H; rewrite IHn; trivial.
Qed.

Lemma Csum_eq_compat : forall Un Vn n,
  (forall j, (j <= n)%nat -> Un j = Vn j) -> sum_f_C0 Un n = sum_f_C0 Vn n.
Proof.
intros Un Vn n H.
induction n.
 apply H; lia.
 simpl; rewrite H; try lia.
 rewrite IHn; trivial.
 intros j Hj.
 apply H; lia.
Qed.

Lemma Cser_cv_eq_compat : forall Un Vn l,
  (forall j, Un j = Vn j) -> Cser_cv Un l -> Cser_cv Vn l.
Proof.
intros Un Vn l H HC.
apply Cseq_cv_eq_compat with (sum_f_C0 Un).
 intro; apply Csum_eq_compat_weak; apply H.
 apply HC.
Qed.
