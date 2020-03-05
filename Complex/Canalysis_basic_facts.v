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

Require Import Cprop_base Ctacfield.
Require Import Cfunctions Cpow.

Require Import Csequence_def.
Require Import Cpser_def Cpser_base_facts.

Require Import Canalysis_def.
Require Import Canalysis_deriv.

Open Scope C_scope.


Lemma growth_rate_Cre : forall (f : C -> C) lb ub f',
  (lb <> ub)%R ->
  Rabs (Ranalysis_def.growth_rate (fun z => Cre (f z)) lb ub - Cre f')%R <= Cnorm (growth_rate f lb ub - f')%C.
Proof.
intros f lb ub f' ublb_neq ;
 unfold Ranalysis_def.growth_rate ; rewrite Cre_minus_compat, <- Cre_div_compat, Cre_minus_compat.
 + etransitivity.
  - eapply Cre_le_Cnorm.
  - rewrite <- IRC_minus_compat ; reflexivity.
 + apply Rminus_eq_contra ; symmetry ; assumption.
Qed.

(****************************)
(** * derivable_pt_lim *)
(****************************)

Lemma derivable_pt_lim_Cpow : forall  (z : C) (n:nat),
      derivable_pt_lim (fun z => z ^ (S n)) z (INC (S n) * z ^ n).
Proof.
 intros z n ; induction n.
 simpl ; rewrite Cmult_1_r ; intros eps eps_pos.
 exists (mkposreal 1 Rlt_0_1) ; intros ; apply Rle_lt_trans with (Cnorm C0).
 right ; apply Cnorm_eq_compat. field; auto.
 rewrite Cnorm_C0. assumption.
 replace (fun z0 : C => z0 ^ S (S n)) with (fun z0 : C => z0 * (z0 ^ (S n))).
 replace  (INC (S (S n)) * z ^ S n) with ((1 * (z ^ (S n))) + z * ((INC (S n) * z ^ n))).
 assert (H' := derivable_pt_lim_id z).
 assert (Main := derivable_pt_lim_mult id (fun z => Cpow z (S n)) z
 1 (INC (S n) * z ^ n) H' IHn).
 apply Main.
 rewrite Cmult_1_l ; simpl ; ring.
 reflexivity.
Qed.

Lemma derivable_pt_lim_gt_pser : forall An z n,
  derivable_pt_lim (fun x : C => gt_pser An x (S n)) z (gt_pser (An_deriv An) z n).
Proof.
intros An z n ; unfold An_deriv, gt_pser, Cseq_mult, Cseq_shift ; induction n.
 simpl ; intros eps eps_pos ; exists  (mkposreal 1 Rlt_0_1) ;
   intros ; apply Rle_lt_trans with (Cnorm C0) ; [right ;
   apply Cnorm_eq_compat ; field | rewrite Cnorm_C0] ; assumption.
 assert (Main := derivable_pt_lim_mult (fun _ => An (S (S n))) (fun z => Cpow z (S (S n)))
 z 0 (INC (S (S n)) * z ^ (S n)) (derivable_pt_lim_const _ _) (derivable_pt_lim_Cpow _ _)).
 rewrite Cmult_0_l, Cadd_0_l in Main.
 replace (INC (S (S n)) * An (S (S n)) * z ^ S n) with (An (S (S n)) * (INC (S (S n)) * z ^ S n)) by ring.
 assumption.
Qed.

Lemma derivable_pt_lim_sum_f_C0 : forall (An : nat -> C -> C) (Bn : nat -> C -> C),
     (forall z n, derivable_pt_lim (An n) z (Bn n z)) -> forall z n, 
     derivable_pt_lim (fun z => sum_f_C0 (fun n => An n z) n) z
     (sum_f_C0 (fun n => Bn n z) n).
Proof.
intros An Bn An_deriv z n ; induction n.
 simpl ; apply An_deriv.
 simpl ; apply derivable_pt_lim_add ; [apply IHn | apply An_deriv].
Qed.

Lemma derivable_pt_lim_partial_sum : forall (An : nat -> C) (z : C) (n : nat),
     derivable_pt_lim (fun z => sum_f_C0 (gt_pser An z) n) z (match n with
     | O => 0
     | S _ => sum_f_C0 (gt_pser (An_deriv An) z) (pred n)
         end).
Proof.
 intros An z n ; induction n.
  unfold gt_pser, Cseq_mult ; simpl ; apply derivable_pt_lim_const.
  destruct n.
   simpl ; rewrite <- Cadd_0_l ; apply derivable_pt_lim_add ; [apply IHn |].
   unfold gt_pser, An_deriv, Cseq_mult, Cseq_shift ; simpl ;  rewrite Cmult_1_r, Cmult_1_l.
   intros eps eps_pos ; exists  (mkposreal 1 Rlt_0_1) ;
   intros ; apply Rle_lt_trans with (Cnorm C0) ; [right ;
   apply Cnorm_eq_compat ; field | rewrite Cnorm_C0] ; assumption.
   simpl ; apply derivable_pt_lim_add.
   apply IHn.
   apply derivable_pt_lim_gt_pser.
Qed.

(****************************)
(** * derivable *)
(****************************)

Lemma derivable_sum_f_C0 : forall (An : nat -> C -> C),
     (forall n, derivable (An n)) -> forall n, derivable (fun z => sum_f_C0 (fun n => An n z) n).
Proof.
intros An An_deriv n ; induction n.
 simpl ; apply An_deriv.
 simpl ; apply derivable_add ; [apply IHn | apply An_deriv].
Qed.

Lemma derivable_Cpow : forall  (n:nat), derivable (fun z => z ^ n).
Proof.
 intro n ; induction n.
 simpl ; apply derivable_const.
 simpl ; apply derivable_mult ; [apply derivable_id | apply IHn].
Qed.
