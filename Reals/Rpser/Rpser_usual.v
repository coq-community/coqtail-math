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

Require Import MyReals MyINR.
Require Import Rsequence_def Rsequence_facts Rsequence_cv_facts Rsequence_sums_facts.
Require Import Rsequence_base_facts Rsequence_rewrite_facts Rsequence_usual_facts.
Require Import Rsequence_subsequence.

Require Import Max.
Require Import Fourier.

Require Import Rpser_def Rpser_def_simpl Rpser_base_facts Rpser_cv_facts Rpser_radius_facts.
Require Import Rpser_sums Rpser_derivative Rpser_derivative_facts.

Require Import Rfunction_def Functions Rpow_facts.

Open Scope R_scope.

(** * Definition of the null power series. *)

Definition zero_seq := 0%Rseq.

Lemma zero_infinite_cv_radius : infinite_cv_radius zero_seq.
Proof.
intro r ; exists 0 ; intros x [n Hn] ; subst ;
 unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, Rseq_constant ;
 rewrite Rmult_0_l, Rabs_R0 ; reflexivity.
Qed.

Lemma Rpser_zero_seq : forall (x : R), Rpser (zero_seq) x 0.
Proof.
intros x eps eps_pos ; exists O ; intros n _ ; unfold R_dist ;
 apply Rle_lt_trans with (Rabs 0) ; [right ; apply Rabs_eq_compat |
 rewrite Rabs_R0 ; assumption].
 unfold Rminus ; rewrite Ropp_0, Rplus_0_r ; induction n ; simpl ;
 [| rewrite Rseq_pps_simpl, IHn] ; unfold Rseq_pps, zero_seq, Rseq_constant, gt_pser, Rseq_mult ;
 simpl ; ring.
Qed.

Definition zero := sum _ zero_infinite_cv_radius.

Lemma zero_is_zero : forall x, zero x = 0.
Proof.
intro x ;
 assert (Hl := sum_sums _ zero_infinite_cv_radius x) ;
 assert (Hr := Rpser_zero_seq x) ;
 apply (Rpser_unique _ _ _ _ Hl Hr).
Qed.

(** * Simplification when zipping with 0 *)

Lemma Rpser_zip_compat_0_l : forall An x la,
  Rpser An (x ^ 2) la ->
  Rpser (Rseq_zip An 0) x la.
Proof.
intros An x la Hla ; replace la with (la + x * 0) by ring ;
 apply Rpser_zip_compat, Rpser_zero_seq ; assumption.
Qed.

Lemma Rpser_zip_compat_0_r : forall An x la,
  Rpser An (x ^ 2) la ->
  Rpser (Rseq_zip 0 An) x (x * la).
Proof.
intros An x la Hla ; replace (x * la) with (0 + x * la) by ring ;
 apply Rpser_zip_compat ; [apply Rpser_zero_seq | assumption].
Qed.

(** * Definition of the constant power series. *)

Definition constant_seq (r : R) (n : nat) := if eq_nat_dec n 0 then r else 0.

Lemma constant_infinite_cv_radius : forall (r : R),
  infinite_cv_radius (constant_seq r).
Proof.
intros r n ; exists (Rabs r) ; intros x [i Hi] ; subst ;
 unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, constant_seq ;
 destruct i ; simpl ; [rewrite Rmult_1_r ; right ; reflexivity |
 rewrite Rmult_0_l, Rabs_R0 ; apply Rabs_pos].
Qed.

Lemma Pser_constant_seq : forall (r : R) (x : R), Pser (constant_seq r) x r.
Proof.
intros r x.
  assert (Hrew : forall n, sum_f_R0 (fun n => (constant_seq r) n * x ^ n) n = r).
   induction n.
   unfold constant_seq ; simpl ; apply Rmult_1_r.
   simpl ; rewrite IHn ; unfold constant_seq ; simpl ; rewrite Rmult_0_l, Rplus_0_r ;
   reflexivity.
intros eps eps_pos ; exists O ; intros n n_lb ; rewrite Hrew, R_dist_eq ;
 assumption.
Qed.

Definition constant (r : R) := sum _ (constant_infinite_cv_radius r).

Lemma constant_is_cst : forall (r : R),
  constant r == (fun _ => r).
Proof.
intros r x ;
 assert (Hl := sum_sums _ (constant_infinite_cv_radius r) x) ;
 assert (Hr := Pser_constant_seq r x) ;
 apply (Rpser_unique _ _ _ _ Hl Hr).
Qed.

(** * Definition of the identity *)

Definition identity_seq (n : nat) := if eq_nat_dec n 1 then 1 else 0.

Lemma identity_infinite_cv_radius : infinite_cv_radius identity_seq.
Proof.
intros r ; exists (Rabs r) ; intros x [i Hi] ; subst ;
unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, identity_seq ;
 destruct (eq_nat_dec i 1) as [Heq|Hneq].
 rewrite Heq ; right ; apply Rabs_eq_compat ; ring.
 rewrite Rmult_0_l, Rabs_R0 ; apply Rabs_pos.
Qed.

Definition identity := sum _ identity_infinite_cv_radius.

(** * Definition of the sum of x^k *)

Definition sum_pow_seq : Rseq := 1.

Lemma sum_pow_cv_radius : finite_cv_radius sum_pow_seq 1.
Proof.
rewrite <- Rinv_1 ; apply Rpser_alembert_finite.
 apply Rgt_not_eq, Rlt_0_1.
 intro ; apply Rgt_not_eq, Rlt_0_1.
 eapply Rseq_cv_eq_compat, Rseq_constant_cv.
  intro ; unfold sum_pow_seq, Rseq_abs, Rseq_div, Rseq_shift, Rseq_constant, Rdiv.
    rewrite Rinv_1, Rmult_1_r ; apply Rabs_R1.
Qed.

Definition sum_pow := sum_r _ _ sum_pow_cv_radius.

Lemma partial_sum_pow_explicit : forall x n,
  (1 - x) * Rseq_pps sum_pow_seq x n = 1 - x ^ S n.
Proof.
intros x n ; induction n.
 unfold Rseq_pps, sum_pow_seq, Rseq_constant ; simpl ;
  rewrite gt_pser_0 ; ring.
 unfold Rseq_pps in * ; rewrite Rseq_sum_simpl, <- tech_pow_Rmult,
  Rmult_plus_distr_l, IHn ; unfold gt_pser, sum_pow_seq, Rseq_constant, Rseq_mult.
  ring.
Qed.

Lemma sum_pow_explicit : forall x, Rabs x < 1 ->
  sum_pow x = / (1 - x).
Proof.
intros x x_in ; eapply Rpser_unique.
 eapply sum_r_sums ; assumption.
 apply Rseq_cv_eq_compat with (Vn := fun n => (1 - Rseq_shift (Rseq_pow x) n) / (1 - x)).
  intro n ; unfold Rseq_shift, Rseq_pow ; rewrite <- partial_sum_pow_explicit ; field.
   apply Rminus_eq_contra ; intro Hf ; apply (Rlt_irrefl 1) ;
   rewrite <- Hf, Rabs_R1 in x_in ; assumption.
 rewrite <- Rmult_1_l ; apply Rseq_cv_mult_compat, Rseq_constant_cv.
 rewrite <- Rminus_0_r ; apply Rseq_cv_minus_compat.
  apply Rseq_constant_cv.
  apply Rseq_cv_shift_compat_reciprocal, Rseq_pow_lt_1_cv_strong ; assumption.
Qed.

(** * Definition of exp, cosine and sine *)

(** Sequences *)

Definition exp_seq (n : nat) := / INR (fact n).

Definition cos_seq : Rseq.
Proof.
unfold Rseq ; apply Rseq_zip.
 intro n ; exact ((-1) ^ n / INR (fact (2 * n))).
 exact zero_seq.
Defined.

Definition sin_seq : Rseq.
Proof.
unfold Rseq ; apply Rseq_zip.
 exact zero_seq.
 intro n ; exact ((-1) ^ n / INR (fact (S (2 * n)))).
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
 intro n ; unfold Rseq_shifts.
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
intros r ; apply Rle_Cv_radius_weak_compat with (| exp_seq |).
 intro n ; unfold cos_seq, exp_seq, Rseq_zip ; destruct (n_modulo_2 n) as [[p Hp] | [p Hp]].
 unfold Rdiv, Rseq_abs ; rewrite Rabs_Rabsolu, Rabs_mult, pow_1_abs, Rmult_1_l ; subst ;
 right ; reflexivity.
 unfold zero_seq, Rseq_constant ; rewrite Rabs_R0 ; apply Rabs_pos.
 rewrite <- Cv_radius_weak_abs ; apply exp_infinite_cv_radius.
Qed.

Lemma sin_infinite_cv_radius : infinite_cv_radius sin_seq.
Proof.
intros r ; apply Rle_Cv_radius_weak_compat with (| exp_seq |)%R.
 intro n ; unfold sin_seq, exp_seq, Rseq_zip ; case (n_modulo_2 n) ; intros [p Hp].
 unfold zero_seq, Rseq_constant ; rewrite Rabs_R0 ; apply Rabs_pos.
 unfold Rdiv, Rseq_abs ; rewrite Rabs_Rabsolu, Rabs_mult, pow_1_abs, Rmult_1_l ;
 subst ; right ; reflexivity.
 rewrite <- Cv_radius_weak_abs ; apply exp_infinite_cv_radius.
Qed.

(** Defintion of the sums *)

Definition Rexp (x : R) := sum  _ exp_infinite_cv_radius x.

Definition cosine (x : R) : R := sum _ cos_infinite_cv_radius x.

Definition sine (x : R) : R := sum _ sin_infinite_cv_radius x.

(** * About the derivatives of these functions *)

(** Links between the sequences *)

Lemma Deriv_exp_seq_simpl : (An_deriv exp_seq == exp_seq)%Rseq.
Proof.
intro n ; unfold exp_seq, An_deriv, Rseq_shift, Rseq_mult.
 replace (fact (S n))%nat with ((S n) * fact n)%nat by reflexivity.
 rewrite mult_INR, Rinv_mult_distr, <- Rmult_assoc, Rinv_r, Rmult_1_l ;
 [reflexivity | | |] ; replace R0 with (INR O) by reflexivity ; apply not_INR ;
 try apply fact_neq_0 ; intuition.
Qed.

Lemma Deriv_cos_seq_simpl : (An_deriv cos_seq == - sin_seq)%Rseq.
Proof.
intro n ; unfold cos_seq, sin_seq, An_deriv, Rseq_shift, Rseq_mult,
 Rseq_opp, Rseq_zip, zero_seq, Rseq_constant ;
 case (n_modulo_2 n) ; intros [p Hp] ; case (n_modulo_2 (S n)) ; intros [q Hq].
  apply False_ind ; omega.
  ring.
 replace q with (S p) by omega ; rewrite Hp, two_Sn, <- Hp.
 rewrite Rmult_comm ; unfold Rdiv ; rewrite Rmult_assoc.
 replace (/ INR (fact (S n)) * INR (S n)) with (/ INR (fact n)).
 simpl ; ring.
 rewrite fact_simpl, mult_INR ; field ; split ; apply not_0_INR ; [apply fact_neq_0 | intuition].
 apply False_ind ; omega.
Qed.

Lemma Deriv_sin_seq_simpl : (An_deriv sin_seq == cos_seq)%Rseq.
Proof.
intro n ; unfold cos_seq, sin_seq, An_deriv, Rseq_shift, Rseq_mult, Rseq_zip,
 zero_seq, Rseq_constant ;
 case (n_modulo_2 n) ; intros [p Hp] ; case (n_modulo_2 (S n)) ; intros [q Hq].
 apply False_ind ; omega.
 rewrite <- Hq ; replace q with p by omega ; rewrite <- Hp.
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
 symmetry ; eapply Rpser_unique_extentionality.
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
 symmetry ; eapply Rpser_unique_extentionality.
 apply Deriv_sin_seq_simpl.
 apply T2.
 apply T1.
Qed.

Lemma sine_eq_Deriv_cosine : forall x, sine x = - Deriv_cosine x.
Proof.
intro x.
 assert (T1 := sum_sums _ sin_infinite_cv_radius x) ;
 assert (T2 := sum_derive_sums _ cos_infinite_cv_radius x).
 symmetry ; apply Rpser_unique_extentionality with (- An_deriv cos_seq)%Rseq (sin_seq) x.
 intro n ; rewrite <- Ropp_involutive ;
 apply Ropp_eq_compat ; apply Deriv_cos_seq_simpl.
 apply Rpser_opp_compat ; apply T2.
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

Lemma derivable_cosine : derivable cosine.
Proof.
intro x ; apply derivable_pt_cosine.
Qed.

Lemma derivable_sine : derivable sine.
Proof.
intro x ; apply derivable_pt_sine.
Qed.

Lemma derive_pt_sine_cosine : forall (x : R) (pr : derivable_pt sine x),
  derive_pt sine x pr = cosine x.
Proof.
intros x pr ; rewrite derive_pt_eq ; apply derivable_pt_lim_sine.
Qed.

Lemma derive_pt_cosine_sine : forall (x : R) (pr : derivable_pt cosine x),
  derive_pt cosine x pr = - sine x.
Proof.
intros x pr ; rewrite derive_pt_eq ; apply derivable_pt_lim_cosine.
Qed.

(* Link with the standard's library definitions. *)

Lemma unfold_plus1 : forall n, (n + 1 = S n)%nat.
Proof.
intros n ; ring.
Qed.

Lemma sin_sine : sin == sine.
Proof.
intro x ; eapply Rpser_unique, sum_sums.
 unfold sin ; destruct (exist_sin (x²)) as [la Hla].
 apply Rpser_zip_compat_0_r.
 unfold Rpser ; rewrite Rseq_cv_eq_compat.
  apply Hla.
  apply Rseq_sum_ext ; intro n ; unfold gt_pser, Rseq_mult, sin_n.
  rewrite <- pow_Rsqr, pow_mult, unfold_plus1 ; reflexivity.
Qed.

Lemma cos_cosine : cos == cosine.
Proof.
intro x ; eapply Rpser_unique, sum_sums.
 unfold cos ; destruct (exist_cos (x²)) as [la Hla].
 apply Rpser_zip_compat_0_l.
 unfold Rpser ; rewrite Rseq_cv_eq_compat.
  apply Hla.
  apply Rseq_sum_ext ; intro n ; unfold gt_pser, Rseq_mult, cos_n.
  rewrite <- pow_Rsqr, pow_mult ; reflexivity.
Qed.

(** * Definition of arctan *)

Definition arctan_seq : Rseq.
Proof.
unfold Rseq ; apply Rseq_zip.
 exact zero_seq.
 intro n ; exact ((- 1) ^ n / INR (S (2 * n))).
Defined.

Require Import MyNNR.

Lemma Rseq_shifts_poly_neq : forall d n k, (0 < k)%nat ->
  Rseq_shifts (Rseq_poly d) k n <> 0.
Proof.
intros d k n Hk ; unfold Rseq_shift, Rseq_poly ;
 apply pow_nonzero, not_0_INR ; omega.
Qed.

Lemma arctan_cv_radius : finite_cv_radius arctan_seq 1.
Proof.
rewrite <- Rsqrt_sqr with (y := nnr_sqr 1) ; [| fourier | simpl ; ring].
 apply finite_cv_radius_zip_compat_r.
  intros ; apply zero_infinite_cv_radius.
  replace (nonneg (nnr_sqr 1)) with (/ 1) by (rewrite Rinv_1 ; simpl ; ring).
 apply Rpser_alembert_finite.
  apply Rgt_not_eq ; fourier.
  intro n ; apply Rmult_integral_contrapositive_currified.
   apply pow_nonzero, Rlt_not_eq ; fourier.
   apply Rinv_neq_0_compat, not_0_INR ; omega.
 assert (Hf : is_extractor (fun n => S (2 * n))) by (intro ; omega) ;
  pose (phi := existT _ _ Hf) ; rewrite Rseq_cv_eq_compat with
  (Vn := (Rseq_poly 1 ⋅ phi / (Rseq_shifts (Rseq_poly 1) 2 ⋅ phi))%Rseq).
 apply Rseq_equiv_cv_div.
  eapply Rseq_equiv_subseq_compat.
   eapply Rseq_poly_shifts_equiv.
  intro ; apply Rseq_shifts_poly_neq ; omega.
 intro n ; unfold Rseq_shift, Rseq_shifts, Rseq_abs, Rseq_div, Rseq_poly, extracted.
 repeat rewrite <- Rabs_Rdiv.
 unfold Rdiv ; do 2 rewrite Rabs_opp1, Rmult_1_l ; rewrite Rinv_involutive.
 rewrite Rabs_right, pow_1. rewrite Rabs_right, pow_1.
 simpl proj1_sig ; simpl mult ; simpl plus ; rewrite <- plus_n_Sm ; apply Rmult_comm.
  apply Rle_ge, pos_INR.
  apply Rle_ge, pos_INR.
  apply Rabs_no_R0, not_0_INR ; omega.
  apply not_0_INR ; omega.
  apply not_0_INR ; omega.
  apply Rmult_integral_contrapositive_currified.
   apply pow_nonzero, Rlt_not_eq ; fourier.
   apply Rinv_neq_0_compat, not_0_INR ; omega.
Qed.

Lemma arctan1_PI4 : Rpser arctan_seq 1 (PI / 4).
Proof.
rewrite <- Rmult_1_l ; apply Rpser_zip_compat_0_r ;
 unfold PI ; destruct exist_PI as [v Hv].
 rewrite Rmult_comm ; unfold Rdiv ; rewrite Rmult_assoc, Rinv_r, Rmult_1_r.
 eapply Rseq_cv_eq_compat, Hv.
 unfold Rseq_pps ; intro n ; apply Rseq_sum_ext ; clear n.
 intro n ; unfold gt_pser, tg_alt, PI_tg, Rseq_mult.
 do 2 rewrite pow1 ; rewrite unfold_plus1, Rmult_1_r ; reflexivity.
 apply Rgt_not_eq ; fourier.
Qed.

Definition arctan := sum_r _ _ arctan_cv_radius.

Lemma arctan_0 : arctan 0 = 0.
Proof.
eapply Rpser_unique ; [eapply sum_r_sums |].
 rewrite Rabs_R0 ; apply Rlt_0_1.
 apply Rseq_cv_eq_compat with (fun _ => 0).
  intro ; rewrite Rseq_pps_0_simpl ; unfold arctan_seq, Rseq_zip.
   case (n_modulo_2 0) ; intros [p Hp] ; [reflexivity | apply False_ind ; omega ].
  apply Rseq_constant_cv.
Qed.