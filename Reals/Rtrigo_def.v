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

Require Import Cprop_base.
Require Import Cnorm.
Require Import Cexp.

Require Export MyReals.
Require Import Rsequence.
Require Import Rsequence_cv_facts.
Require Import Rsequence_base_facts.

Require Import Max.
Require Import Fourier.

Require Import Rpser_def.
Require Import Rpser_facts.

Open Scope R_scope.

Definition cos_seq (n : nat) : R.
Proof.
intro n ; destruct (n_modulo_2 n) as [ [p Hp] | [p Hp]].
 apply ((-1) ^ p / INR (fact n)).
 apply 0.
Defined.

Lemma even_odd_boundedness : forall (An : nat -> R) (M1 M2 : R),
     Rseq_bound (fun n => An (2 * n)%nat) M1 ->
     Rseq_bound (fun n => An (S (2 * n))) M2 ->
     Rseq_bound An (Rmax M1 M2).
Proof.
intros An M1 M2 HM1 HM2 n ; destruct (n_modulo_2 n) as [n_even | n_odd].
 destruct n_even as [p Hp] ; rewrite Hp ; apply Rle_trans with M1 ; [apply HM1 | apply RmaxLess1].
 destruct n_odd as [p Hp] ; rewrite Hp ; apply Rle_trans with M2 ; [apply HM2 | apply RmaxLess2].
Qed.

Lemma Rle_cv_radius_compat : forall (An Bn : nat -> R) (r : R),
      (forall n, Rabs (Bn n) <= Rabs (An n)) ->
      Cv_radius_weak An r ->
      Cv_radius_weak Bn r.
Proof.
intros An Bn r Bn_le_An [M HM] ; exists M ; intros x [n Hn] ;
 rewrite Hn ; apply Rle_trans with (gt_abs_Pser An r n) ;
 [| apply HM ; exists n ; reflexivity].
 unfold gt_abs_Pser ; do 2 rewrite Rabs_mult ;
 apply Rmult_le_compat_r ; [apply Rabs_pos | apply Bn_le_An].
Qed.


Lemma cos_infinite_cv_radius : infinite_cv_radius cos_seq.
Proof.
intros r ; apply Rle_cv_radius_compat with (fun n => Cnorm (exp_seq n))%R.
 intro n ; unfold cos_seq, exp_seq ; destruct (n_modulo_2 n) as [[p Hp] | [p Hp]].
 unfold Rdiv ;  rewrite Cnorm_inv, <- IRC_INR_INC, Cnorm_IRC_Rabs,
 <- Rabs_Rinv, Rabs_Rabsolu, Rabs_mult, pow_1_abs, Rmult_1_l.
 right ; reflexivity.
 apply not_0_INR ; apply fact_neq_0.
 apply not_0_INC ; apply fact_neq_0.
 rewrite Rabs_R0 ; apply Rabs_pos.
 apply Cpser_def.Cv_radius_weak_Cnorm_compat2 ; apply exp_infinite_cv_radius.
Qed.

Definition cosine (x : R) : R := sum _ cos_infinite_cv_radius x.

Definition Deriv_cos (x : R) : R := sum_derive _ cos_infinite_cv_radius x.