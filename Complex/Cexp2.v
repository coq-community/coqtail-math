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

Require Import Rsequence.
Require Import Rsequence_facts.
Require Import Rsequence_cv_facts.
Require Import Rsequence_usual_facts.
Require Import MyRIneq.

Require Import Cprop_base.
Require Import Csequence.
Require Import Csequence_facts.
Require Import Cpser_def.
Require Import Cpser_facts.
Require Import Canalysis_def.

Open Scope C_scope.

(** * Definition and manipulation of the general term of the power serie of the exponential *)

Definition exp_seq (n : nat) := / INC (fact n).

Lemma exp_seq_neq : forall n : nat, exp_seq n <> 0.
Proof.
intro n ; unfold exp_seq ; apply Cinv_neq_0_compat ;
 apply not_0_INC ; apply fact_neq_0.
Qed.

Lemma Cdiv_exp_seq_simpl : forall n, (exp_seq (S n)) / (exp_seq n) = / INC (S n).
Proof.
intros n ; unfold exp_seq.
 replace (fact (S n))%nat with ((S n) * fact n)%nat by reflexivity ;
 unfold Cdiv ; rewrite mult_INC, Cinv_involutive ;
 [rewrite Cinv_mult_distr ;
  [rewrite Cmult_assoc, Cinv_l, Cmult_1_r ;
   [reflexivity |] | |] |] ;
   apply not_0_INC ; auto ;  apply fact_neq_0.
Qed.

Lemma Deriv_exp_seq_simpl : forall n, An_deriv exp_seq n = exp_seq n.
Proof.
intro n ; unfold exp_seq, An_deriv.
 replace (fact (S n))%nat with ((S n) * fact n)%nat by reflexivity.
 rewrite mult_INC, Cinv_mult_distr, <- Cmult_assoc, Cinv_r, Cmult_1_l ;
 [reflexivity | | |] ; replace C0 with (INC O) by reflexivity ; apply not_INC ;
 try apply fact_neq_0 ; intuition.
Qed.

(** * This power serie has a radius of convergence that is infinite *)

Lemma exp_infinite_cv_radius : infinite_cv_radius exp_seq.
Proof.
intros r.
 pose (M := (/ (Rabs r + 1))%R) ; assert (M_pos : 0 < M).
  unfold M ; apply Rinv_0_lt_compat ;
  apply Rplus_le_lt_0_compat ; [apply Rabs_pos | apply Rlt_0_1].
 apply (Cpser_alembert_prelim2 exp_seq M M_pos exp_seq_neq).

assert (t : (1 > 0)%nat) by constructor ;
 assert (H := Rseq_poly_cv 1 t) ;
 assert (H2 := Rseq_cv_pos_infty_shift_compat_reciprocal _ H) ;
 assert (H3 := Rseq_cv_pos_infty_inv_compat _ H2) ;
 clear t H H2 ; destruct (H3 _ M_pos) as [N HN] ; exists N ;
 intros n.
 rewrite Cdiv_exp_seq_simpl, <- IRC_INR_INC, <- Cinv_IRC_Rinv.
 rewrite Cnorm_IRC_Rabs.
 apply Rle_trans with (R_dist ((/ Rseq_shift (Rseq_poly 1))%Rseq (N + n)%nat) 0).
 right ; unfold R_dist, Rseq_shift, Rseq_poly, pow ; apply Rabs_eq_compat ;
 rewrite Rminus_0_r, <- (Rmult_1_r (INR (S (N + n)))) ; reflexivity.
 left ; apply HN ; intuition.
 apply not_0_INR ; intuition.

unfold M ; rewrite Rinv_involutive ; [| apply Rgt_not_eq ; apply Rplus_le_lt_0_compat ;
 [apply Rabs_pos | apply Rlt_0_1]] ; intuition.
Qed.

Definition Cexp (z : C) := sum  _ exp_infinite_cv_radius z.

Definition Deriv_Cexp (z : C) := sum_derive _ exp_infinite_cv_radius z.


(** * The exponential is its own derivative *)

Lemma Cexp_eq_Deriv_Cexp : forall z, Cexp z = Deriv_Cexp z.
Proof.
intro z.
 assert (T1 := sum_sums _ exp_infinite_cv_radius z) ;
 assert (T2 := sum_derive_sums _ exp_infinite_cv_radius z).
 symmetry ; eapply Pser_unique_extentionality.
 apply Deriv_exp_seq_simpl.
 apply T2.
 apply T1.
Qed.

Lemma derivable_pt_lim_Cexp : forall z, derivable_pt_lim Cexp z (Cexp z).
Proof.
intro z ; rewrite Cexp_eq_Deriv_Cexp ;
 apply derivable_pt_lim_sum.
Qed.

(** ** Euler's Formula*)

Lemma Cexp_exp_compat : forall a : R, exp (a) = Cre (Cexp (a +i 0))
/\ Cim (Cexp (a +i 0)) = 0%R.
Proof.
intros a ; unfold exp, Cexp ; destruct (exist_exp a) as (l, H).
 pose (l1 := sum exp_seq exp_infinite_cv_radius (a +i  0)) ;
 assert (H1 := sum_sums _ exp_infinite_cv_radius (a +i 0)) ;
 replace (sum exp_seq exp_infinite_cv_radius (a +i  0)) with l1 in * by reflexivity.
simpl.

split.
apply (Rseq_cv_unique (sum_f_R0 (fun j : nat => (/ INR (fact j) * a ^ j)%R))).
 apply H.
  apply Rseq_cv_eq_compat with (fun n => Cre (sum_f_C0 (fun j : nat => / INC (fact j) * (a +i  0) ^ j) n)).
   intro n ; induction n.
  simpl ; field.
  rewrite sum_f_C0_simpl, tech5, <- Cre_add_compat, IHn ;
  apply Rplus_eq_compat_l.
  rewrite Cre_mul, Cpow_Cim_0, Cpow_Cre_0, Rmult_0_r, Rminus_0_r.
  rewrite INC_inv_Cre_INR ; [reflexivity | apply fact_neq_0].
 apply (Cseq_Rseq_Rseq_equiv _ _) ; apply Pser_Cseqcv_link ; unfold exp_seq in H1 ; apply H1.

 apply (Rseq_cv_unique (fun n => Cim (sum_f_C0 (fun j : nat => / INC (fact j) * (a +i  0) ^ j) n))).
  apply (Cseq_Rseq_Rseq_equiv _ _) ; apply Pser_Cseqcv_link ; unfold exp_seq in H1 ; apply H1.
  apply (Rseq_cv_eq_compat R0) ; [| apply Rseq_constant_cv].
  intro n ; induction n ; unfold Rseq_constant in *.
  simpl ; field.
  rewrite sum_f_C0_simpl, <- Cim_add_compat, <- IHn, Cim_mul, Cpow_Cim_0,
  Cpow_Cre_0, INC_inv_Cim_INR ; [ring | apply fact_neq_0].
Qed.
