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

Require Export MyReals.
Require Import Rsequence.
Require Import Rsequence_facts.
Require Import Rsequence_cv_facts.
Require Import Rsequence_base_facts.
Require Import Rsequence_usual_facts.

Require Import Max.
Require Import Fourier.

Require Import Rpser_def.
Require Import Rpser_facts.

Open Scope R_scope.

(** * Definition of exp, cosine and sine *)

(** Sequences *)

Definition exp_seq (n : nat) := / INR (fact n).

Definition cos_seq : nat -> R.
Proof.
intro n ; destruct (n_modulo_2 n) as [ [p Hp] | [p Hp]].
 apply ((-1) ^ p / INR (fact n)).
 apply 0.
Defined.

Definition sin_seq : nat -> R.
Proof.
intro n ; case (n_modulo_2 n) ; intros [p Hp].
 apply 0.
 apply ((-1) ^ p / INR (fact n)).
Defined.

(** Infinite cv radius *)

Lemma exp_seq_neq : forall n : nat, exp_seq n <> 0.
Proof.
intro n ; unfold exp_seq ; apply Rinv_neq_0_compat ;
 apply not_0_INR ; apply fact_neq_0.
Qed.

Lemma Rdiv_exp_seq_simpl : forall n, (exp_seq (S n)) / (exp_seq n) = / INR (S n).
Proof.
intros n ; unfold exp_seq.
 replace (fact (S n))%nat with ((S n) * fact n)%nat by reflexivity ;
 unfold Rdiv ; rewrite mult_INR, Rinv_involutive ;
 [rewrite Rinv_mult_distr ;
  [rewrite Rmult_assoc, Rinv_l, Rmult_1_r ;
   [reflexivity |] | |] |] ;
   apply not_0_INR ; auto ;  apply fact_neq_0.
Qed.

Lemma exp_infinite_cv_radius : infinite_cv_radius exp_seq.
Proof.
intros r.
 pose (M := (/ (Rabs r + 1))%R) ; assert (M_pos : 0 < M).
  unfold M ; apply Rinv_0_lt_compat ;
  apply Rplus_le_lt_0_compat ; [apply Rabs_pos | apply Rlt_0_1].
 apply (Rpser_alembert_prelim2 exp_seq M M_pos exp_seq_neq).

assert (t : (1 > 0)%nat) by constructor ;
 assert (H := Rseq_poly_cv 1 t) ;
 assert (H2 := Rseq_cv_pos_infty_shift_compat_reciprocal _ H) ;
 assert (H3 := Rseq_cv_pos_infty_inv_compat _ H2) ;
 clear t H H2 ; destruct (H3 _ M_pos) as [N HN] ; exists N ;
 intros n.
 rewrite Rdiv_exp_seq_simpl ;
 apply Rle_trans with (R_dist ((/ Rseq_shift (Rseq_poly 1))%Rseq (N + n)%nat) 0).
 right ; unfold R_dist, Rseq_shift, Rseq_poly, pow ; apply Rabs_eq_compat ;
 rewrite Rminus_0_r, <- (Rmult_1_r (INR (S (N + n)))) ; reflexivity.
 left ; apply HN ; intuition.
 unfold M ; rewrite Rinv_involutive ; [| apply Rgt_not_eq ; apply Rplus_le_lt_0_compat ;
 [apply Rabs_pos | apply Rlt_0_1]] ; intuition.
Qed.

Lemma cos_infinite_cv_radius : infinite_cv_radius cos_seq.
Proof.
intros r ; apply Rle_cv_radius_compat with (fun n => Rabs (exp_seq n))%R.
 intro n ; unfold cos_seq, exp_seq ; destruct (n_modulo_2 n) as [[p Hp] | [p Hp]].
 unfold Rdiv ;  rewrite Rabs_Rabsolu, Rabs_mult, pow_1_abs, Rmult_1_l ; right ; reflexivity.
 rewrite Rabs_R0 ; apply Rabs_pos.
 apply Cv_radius_weak_Rabs_compat ; apply exp_infinite_cv_radius.
Qed.

Lemma sin_infinite_cv_radius : infinite_cv_radius sin_seq.
Proof.
intros r ; apply Rle_cv_radius_compat with (fun n => Rabs (exp_seq n))%R.
 intro n ; unfold sin_seq, exp_seq ; case (n_modulo_2 n) ; intros [p Hp].
 rewrite Rabs_R0 ; apply Rabs_pos.
 unfold Rdiv ;  rewrite Rabs_Rabsolu, Rabs_mult, pow_1_abs, Rmult_1_l ; right ; reflexivity.
 apply Cv_radius_weak_Rabs_compat ; apply exp_infinite_cv_radius.
Qed.

(** Defintion of the sums *)

Definition Rexp (x : R) := sum  _ exp_infinite_cv_radius x.

Definition cosine (x : R) : R := sum _ cos_infinite_cv_radius x.

Definition sine (x : R) : R := sum _ sin_infinite_cv_radius x.

(** * About the derivatives of these functions *)

(** Links between the sequences *)

Lemma Deriv_exp_seq_simpl : forall n, An_deriv exp_seq n = exp_seq n.
Proof.
intro n ; unfold exp_seq, An_deriv.
 replace (fact (S n))%nat with ((S n) * fact n)%nat by reflexivity.
 rewrite mult_INR, Rinv_mult_distr, <- Rmult_assoc, Rinv_r, Rmult_1_l ;
 [reflexivity | | |] ; replace R0 with (INR O) by reflexivity ; apply not_INR ;
 try apply fact_neq_0 ; intuition.
Qed.

Lemma Deriv_cos_seq_simpl : forall n, An_deriv cos_seq n = (- sin_seq)%Rseq n.
intro n ; unfold cos_seq, sin_seq, An_deriv, Rseq_opp ;
 case (n_modulo_2 n) ; intros [p Hp] ;
 case (n_modulo_2 (S n)) ; intros [p' Hp'].
 apply False_ind ; omega.
 ring.
 replace p' with (S p) by omega.
 rewrite Rmult_comm ; unfold Rdiv ; rewrite Rmult_assoc.
 replace (/ INR (fact (S n)) * INR (S n)) with (/ INR (fact n)).
 simpl ; ring.
 rewrite fact_simpl, mult_INR ; field ; split ; apply not_0_INR ; [apply fact_neq_0 | intuition].
 apply False_ind ; omega.
Qed.

Lemma Deriv_sin_seq_simpl : forall n, An_deriv sin_seq n = cos_seq n.
intro n ; unfold cos_seq, sin_seq, An_deriv ;
 case (n_modulo_2 n) ; intros [p Hp] ;
 case (n_modulo_2 (S n)) ; intros [p' Hp'].
 apply False_ind ; omega.
 replace p' with p by omega.
 rewrite Rmult_comm ; unfold Rdiv ; rewrite Rmult_assoc.
 replace (/ INR (fact (S n)) * INR (S n)) with (/ INR (fact n)).
 simpl ; ring.
 rewrite fact_simpl, mult_INR ; field ; split ; apply not_0_INR ; [apply fact_neq_0 | intuition].
 ring.
 apply False_ind ; omega.
Qed.

(** Definition of the derivatives *)

Definition Deriv_Rexp (x : R) := sum_derive _ exp_infinite_cv_radius x.

Definition Deriv_cosine (x : R) := sum_derive _ cos_infinite_cv_radius x.

Definition Deriv_sine (x : R) := sum_derive _ sin_infinite_cv_radius x.

(** The exponential is its own derivative *)

Lemma Rexp_eq_Deriv_Rexp : forall x, Rexp x = Deriv_Rexp x.
Proof.
intro x.
 assert (T1 := sum_sums _ exp_infinite_cv_radius x) ;
 assert (T2 := sum_derive_sums _ exp_infinite_cv_radius x).
 symmetry ; eapply Pser_unique_extentionality.
 apply Deriv_exp_seq_simpl.
 apply T2.
 apply T1.
Qed.

(** Cosine & sine are each other derivative *)

Lemma cosine_eq_Deriv_sine : forall x, cosine x = Deriv_sine x.
Proof.
intro x.
 assert (T1 := sum_sums _ cos_infinite_cv_radius x) ;
 assert (T2 := sum_derive_sums _ sin_infinite_cv_radius x).
 symmetry ; eapply Pser_unique_extentionality.
 apply Deriv_sin_seq_simpl.
 apply T2.
 apply T1.
Qed.

Lemma sine_eq_Deriv_cosine : forall x, sine x = - Deriv_cosine x.
Proof.
intro x.
 assert (T1 := sum_sums _ sin_infinite_cv_radius x) ;
 assert (T2 := sum_derive_sums _ cos_infinite_cv_radius x).
 symmetry ; apply Pser_unique_extentionality with (- An_deriv cos_seq)%Rseq (sin_seq) x.
 intro n ; rewrite <- Ropp_involutive ;
 apply Ropp_eq_compat ; apply Deriv_cos_seq_simpl.
 apply Pser_opp_compat ; apply T2.
 apply T1.
Qed.

(** Conclusions *)

Lemma derivable_pt_lim_Rexp : forall x, derivable_pt_lim Rexp x (Rexp x).
Proof.
intro x ; rewrite Rexp_eq_Deriv_Rexp ;
 apply derivable_pt_lim_sum.
Qed.

Lemma derivable_pt_lim_cosine : forall x, derivable_pt_lim cosine x (- sine x).
Proof.
intro x ; rewrite sine_eq_Deriv_cosine, Ropp_involutive ;
 apply derivable_pt_lim_sum.
Qed.

Lemma derivable_pt_lim_sine : forall x, derivable_pt_lim sine x (cosine x).
Proof.
intro x ; rewrite cosine_eq_Deriv_sine ;
 apply derivable_pt_lim_sum.
Qed.

Lemma derivable_pt_Rexp : forall x, derivable_pt Rexp x.
Proof.
intro x ; exists (Rexp x) ; apply derivable_pt_lim_Rexp.
Qed.

Lemma derivable_pt_cosine : forall x, derivable_pt cosine x.
Proof.
intro x ; exists (- sine x) ; apply derivable_pt_lim_cosine.
Qed.

Lemma derivable_pt_sine : forall x, derivable_pt sine x.
Proof.
intro x ; exists (cosine x) ; apply derivable_pt_lim_sine.
Qed.
